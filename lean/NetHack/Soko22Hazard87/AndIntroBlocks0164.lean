import NetHack.Soko22Hazard87.AndIntroBlocks0163
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro41000 (p : Pattern) (ha : d131547 p = 1) (hb : d181291 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131528 q = 1) (hb : d181260 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131528, d181260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40994 q ha hb
    | true =>
      simp only [d131528, d181260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131529 q = 1) (hb : d181261 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131529, d181261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131529, d181261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131544 q = 1) (hb : d181288 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131544, d181288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131544, d181288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131545 q = 1) (hb : d181289 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131545, d181289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131545, d181289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131546 q = 1) (hb : d181290 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131546, d181290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131546, d181290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131547 q = 1) (hb : d181291 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131547, d181291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131547, d181291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41001 (p : Pattern) (ha : d131579 p = 1) (hb : d181297 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131574 q = 1) (hb : d181292 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131574, d181292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41000 q ha hb
    | true =>
      simp only [d131574, d181292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131575 q = 1) (hb : d181293 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131575, d181293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131575, d181293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131576 q = 1) (hb : d181294 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131576, d181294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131576, d181294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131577 q = 1) (hb : d181295 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131577, d181295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131577, d181295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131578 q = 1) (hb : d181296 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131578, d181296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131578, d181296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131579 q = 1) (hb : d181297 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131579, d181297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131579, d181297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41002 (p : Pattern) (ha : d131585 p = 1) (hb : d181303 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131573 q = 1) (hb : d181287 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131573, d181287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131573, d181287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40999 q ha hb
  have h2 (q : Pattern) (ha : d131580 q = 1) (hb : d181298 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131580, d181298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131580, d181298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41001 q ha hb
  have h3 (q : Pattern) (ha : d131581 q = 1) (hb : d181299 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131581, d181299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131581, d181299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131582 q = 1) (hb : d181300 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131582, d181300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131582, d181300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131583 q = 1) (hb : d181301 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131583, d181301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131583, d181301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131584 q = 1) (hb : d181302 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131584, d181302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131584, d181302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131585 q = 1) (hb : d181303 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131585, d181303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131585, d181303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41003 (p : Pattern) (ha : d131591 p = 1) (hb : d181309 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131586 q = 1) (hb : d181304 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131586, d181304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131586, d181304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41002 q ha hb
  have h2 (q : Pattern) (ha : d131587 q = 1) (hb : d181305 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131587, d181305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131587, d181305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131588 q = 1) (hb : d181306 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131588, d181306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131588, d181306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131589 q = 1) (hb : d181307 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131589, d181307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131589, d181307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131590 q = 1) (hb : d181308 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131590, d181308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131590, d181308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131591 q = 1) (hb : d181309 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131591, d181309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131591, d181309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41004 (p : Pattern) (ha : d131609 p = 1) (hb : d181323 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1853 q = 1) (hb : d53179 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1853, d53179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1853, d53179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro230 q ha hb
  have h2 (q : Pattern) (ha : d19223 q = 1) (hb : d131595 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19223, d131595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19223, d131595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53107 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d131596 q = 1) (hb : d181313 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131596, d181313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d131596, d181313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d131597 q = 1) (hb : d181314 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131597, d181314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131597, d181314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d17004 q = 1) (hb : d127738 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17004, d127738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17004, d127738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23338 q ha hb
  have h7 (q : Pattern) (ha : d19226 q = 1) (hb : d131598 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19226, d131598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19226, d131598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d101465 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d131599 q = 1) (hb : d181315 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131599, d181315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d131599, d181315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d131600 q = 1) (hb : d181316 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131600, d181316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d131600, d181316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d131601 q = 1) (hb : d181317 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131601, d181317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131601, d181317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15380 q = 1) (hb : d123419 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15380, d123419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15380, d123419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23339 q ha hb
  have h13 (q : Pattern) (ha : d19230 q = 1) (hb : d131602 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19230, d131602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19230, d131602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d101475 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d131603 q = 1) (hb : d181318 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131603, d181318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d131603, d181318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d131604 q = 1) (hb : d181319 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131604, d181319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d131604, d181319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d15387 q = 1) (hb : d123426 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15387, d123426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15387, d123426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23341 q ha hb
  have h18 (q : Pattern) (ha : d19233 q = 1) (hb : d131605 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19233, d131605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d19233, d131605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d101492 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d131606 q = 1) (hb : d181320 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131606, d181320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d131606, d181320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d131607 q = 1) (hb : d181321 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131607, d181321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d131607, d181321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d131608 q = 1) (hb : d181322 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131608, d181322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d131608, d181322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d131609 q = 1) (hb : d181323 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d131609, d181323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d131609, d181323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro41005 (p : Pattern) (ha : d131621 p = 1) (hb : d181332 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1857 q = 1) (hb : d53183 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1857, d53183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1857, d53183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro205 q ha hb
  have h2 (q : Pattern) (ha : d19238 q = 1) (hb : d131610 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19238, d131610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19238, d131610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52997 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d131611 q = 1) (hb : d181324 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131611, d181324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d131611, d181324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d131612 q = 1) (hb : d181325 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131612, d181325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131612, d181325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d17011 q = 1) (hb : d127745 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17011, d127745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17011, d127745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23343 q ha hb
  have h7 (q : Pattern) (ha : d19241 q = 1) (hb : d131613 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19241, d131613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19241, d131613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d101503 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d131614 q = 1) (hb : d181326 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131614, d181326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d131614, d181326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d131615 q = 1) (hb : d181327 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131615, d181327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d131615, d181327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d131616 q = 1) (hb : d181328 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131616, d181328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131616, d181328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15387 q = 1) (hb : d123426 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15387, d123426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15387, d123426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23341 q ha hb
  have h13 (q : Pattern) (ha : d19233 q = 1) (hb : d131605 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19233, d131605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19233, d131605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d101492 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d131606 q = 1) (hb : d181320 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131606, d181320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d131606, d181320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d131607 q = 1) (hb : d181321 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131607, d181321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d131607, d181321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d15397 q = 1) (hb : d123436 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, d123436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15397, d123436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23330 q ha hb
  have h18 (q : Pattern) (ha : d19245 q = 1) (hb : d131617 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19245, d131617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d19245, d131617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d101514 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d131618 q = 1) (hb : d181329 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131618, d181329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d131618, d181329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d131619 q = 1) (hb : d181330 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131619, d181330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d131619, d181330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d131620 q = 1) (hb : d181331 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131620, d181331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d131620, d181331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d131621 q = 1) (hb : d181332 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d131621, d181332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d131621, d181332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro41006 (p : Pattern) (ha : d131630 p = 1) (hb : d181340 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13486 q = 1) (hb : d113708 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13486, d113708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13486, d113708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23345 q ha hb
  have h2 (q : Pattern) (ha : d19253 q = 1) (hb : d131625 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19253, d131625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19253, d131625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d101528 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d131626 q = 1) (hb : d181336 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131626, d181336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d131626, d181336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d131627 q = 1) (hb : d181337 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131627, d181337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131627, d181337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d15397 q = 1) (hb : d123436 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, d123436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15397, d123436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23330 q ha hb
  have h7 (q : Pattern) (ha : d19245 q = 1) (hb : d131617 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19245, d131617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19245, d131617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d101514 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d131618 q = 1) (hb : d181329 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131618, d181329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d131618, d181329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d131619 q = 1) (hb : d181330 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131619, d181330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d131619, d181330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d131628 q = 1) (hb : d181338 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131628, d181338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131628, d181338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d131629 q = 1) (hb : d181339 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131629, d181339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d131629, d181339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d131630 q = 1) (hb : d181340 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d131630, d181340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d131630, d181340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro41007 (p : Pattern) (ha : d131642 p = 1) (hb : d181350 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1862 q = 1) (hb : d53188 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1862, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1862, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro208 q ha hb
  have h2 (q : Pattern) (ha : d19263 q = 1) (hb : d131635 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19263, d131635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19263, d131635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d131636 q = 1) (hb : d181345 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131636, d181345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d131636, d181345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d131637 q = 1) (hb : d181346 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131637, d181346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131637, d181346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d17027 q = 1) (hb : d127761 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17027, d127761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17027, d127761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23331 q ha hb
  have h7 (q : Pattern) (ha : d19266 q = 1) (hb : d131638 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19266, d131638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19266, d131638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d101544 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d131639 q = 1) (hb : d181347 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131639, d181347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d131639, d181347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d131640 q = 1) (hb : d181348 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131640, d181348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d131640, d181348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d131641 q = 1) (hb : d181349 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131641, d181349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131641, d181349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15397 q = 1) (hb : d123436 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, d123436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15397, d123436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23330 q ha hb
  have h13 (q : Pattern) (ha : d19245 q = 1) (hb : d131617 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19245, d131617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19245, d131617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d101514 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d131618 q = 1) (hb : d181329 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131618, d181329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d131618, d181329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d131619 q = 1) (hb : d181330 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131619, d181330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d131619, d181330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d131629 q = 1) (hb : d181339 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131629, d181339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d131629, d181339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d131642 q = 1) (hb : d181350 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d131642, d181350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d131642, d181350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro41008 (p : Pattern) (ha : d131654 p = 1) (hb : d181360 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6496 q = 1) (hb : d76225 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6496, d76225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6496, d76225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7964 q ha hb
  have h2 (q : Pattern) (ha : d19274 q = 1) (hb : d131646 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19274, d131646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19274, d131646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d69222 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d131647 q = 1) (hb : d181354 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131647, d181354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d131647, d181354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d131648 q = 1) (hb : d181355 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131648, d181355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131648, d181355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131649 q = 1) (hb : d181356 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131649, d181356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131649, d181356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d15412 q = 1) (hb : d123451 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15412, d123451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15412, d123451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23333 q ha hb
  have h8 (q : Pattern) (ha : d19278 q = 1) (hb : d131650 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19278, d131650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19278, d131650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d101564 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d131651 q = 1) (hb : d181357 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131651, d181357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d131651, d181357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d131652 q = 1) (hb : d181358 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131652, d181358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d131652, d181358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d131653 q = 1) (hb : d181359 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131653, d181359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d131653, d181359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d131654 q = 1) (hb : d181360 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d131654, d181360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131654, d181360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro41009 (p : Pattern) (ha : d131671 p = 1) (hb : d181366 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131622 q = 1) (hb : d181333 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131622, d181333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41004 q ha hb
    | true =>
      simp only [d131622, d181333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41005 q ha hb
  have h2 (q : Pattern) (ha : d131623 q = 1) (hb : d181334 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131623, d181334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131623, d181334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131624 q = 1) (hb : d181335 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131624, d181335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131624, d181335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131631 q = 1) (hb : d181341 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131631, d181341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41005 q ha hb
    | true =>
      simp only [d131631, d181341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41006 q ha hb
  have h5 (q : Pattern) (ha : d131632 q = 1) (hb : d181342 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131632, d181342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131632, d181342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131633 q = 1) (hb : d181343 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131633, d181343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131633, d181343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131634 q = 1) (hb : d181344 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131634, d181344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131634, d181344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131643 q = 1) (hb : d181351 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131643, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41005 q ha hb
    | true =>
      simp only [d131643, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41007 q ha hb
  have h9 (q : Pattern) (ha : d131644 q = 1) (hb : d181352 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131644, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131644, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d131645 q = 1) (hb : d181353 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131645, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131645, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d131655 q = 1) (hb : d181361 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131655, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41007 q ha hb
    | true =>
      simp only [d131655, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41008 q ha hb
  have h12 (q : Pattern) (ha : d131656 q = 1) (hb : d181362 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131656, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131656, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d131657 q = 1) (hb : d181363 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131657, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131657, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d131658 q = 1) (hb : d181364 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131658, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d131658, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d131659 q = 1) (hb : d181365 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d131659, d181365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131659, d181365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d131670 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d131671 q = 1) (hb : d181366 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131671, d181366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d131671, d181366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro41010 (p : Pattern) (ha : d131678 p = 1) (hb : d181371 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131643 q = 1) (hb : d181351 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131643, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41005 q ha hb
    | true =>
      simp only [d131643, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41007 q ha hb
  have h2 (q : Pattern) (ha : d131644 q = 1) (hb : d181352 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131644, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131644, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131645 q = 1) (hb : d181353 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131645, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131645, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131655 q = 1) (hb : d181361 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131655, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41007 q ha hb
    | true =>
      simp only [d131655, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41008 q ha hb
  have h5 (q : Pattern) (ha : d131656 q = 1) (hb : d181362 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131656, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131656, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131657 q = 1) (hb : d181363 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131657, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131657, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131658 q = 1) (hb : d181364 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131658, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131658, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131674 q = 1) (hb : d181369 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131674, d181369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131674, d181369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d131675 q = 1) (hb : d181370 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d131675, d181370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131675, d181370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d131677 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d131678 q = 1) (hb : d181371 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131678, d181371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d131678, d181371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro41011 (p : Pattern) (ha : d131684 p = 1) (hb : d181377 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131672 q = 1) (hb : d181367 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131672, d181367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41009 q ha hb
    | true =>
      simp only [d131672, d181367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131673 q = 1) (hb : d181368 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131673, d181368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131673, d181368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131679 q = 1) (hb : d181372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131679, d181372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41010 q ha hb
    | true =>
      simp only [d131679, d181372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131680 q = 1) (hb : d181373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131680, d181373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131680, d181373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131681 q = 1) (hb : d181374 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131681, d181374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131681, d181374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131682 q = 1) (hb : d181375 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131682, d181375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131682, d181375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131683 q = 1) (hb : d181376 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131683, d181376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131683, d181376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d131684 q = 1) (hb : d181377 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131684, d181377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131684, d181377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41012 (p : Pattern) (ha : d131689 p = 1) (hb : d181381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1868 q = 1) (hb : d53194 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1868, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro209 q ha hb
  have h2 (q : Pattern) (ha : d19313 q = 1) (hb : d131685 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19313, d131685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19313, d131685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d131686 q = 1) (hb : d181378 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131686, d181378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d131686, d181378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d131687 q = 1) (hb : d181379 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131687, d181379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131687, d181379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131688 q = 1) (hb : d181380 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131688, d181380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131688, d181380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d15412 q = 1) (hb : d123451 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15412, d123451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15412, d123451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23333 q ha hb
  have h8 (q : Pattern) (ha : d19278 q = 1) (hb : d131650 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19278, d131650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19278, d131650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d101564 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d131651 q = 1) (hb : d181357 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131651, d181357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d131651, d181357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d131652 q = 1) (hb : d181358 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131652, d181358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d131652, d181358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d131653 q = 1) (hb : d181359 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131653, d181359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d131653, d181359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d131689 q = 1) (hb : d181381 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d131689, d181381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131689, d181381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro41013 (p : Pattern) (ha : d131699 p = 1) (hb : d181387 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131690 q = 1) (hb : d181382 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131690, d181382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41007 q ha hb
    | true =>
      simp only [d131690, d181382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41012 q ha hb
  have h2 (q : Pattern) (ha : d131691 q = 1) (hb : d181383 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131691, d181383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131691, d181383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131692 q = 1) (hb : d181384 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131692, d181384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131692, d181384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131693 q = 1) (hb : d181385 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131693, d181385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131693, d181385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131694 q = 1) (hb : d181386 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d131694, d181386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131694, d181386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d131698 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d131699 q = 1) (hb : d181387 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131699, d181387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131699, d181387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro41014 (p : Pattern) (ha : d131705 p = 1) (hb : d181393 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131679 q = 1) (hb : d181372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131679, d181372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41010 q ha hb
    | true =>
      simp only [d131679, d181372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131680 q = 1) (hb : d181373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131680, d181373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131680, d181373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131700 q = 1) (hb : d181388 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131700, d181388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41013 q ha hb
    | true =>
      simp only [d131700, d181388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131701 q = 1) (hb : d181389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131701, d181389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131701, d181389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131702 q = 1) (hb : d181390 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131702, d181390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131702, d181390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131703 q = 1) (hb : d181391 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131703, d181391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131703, d181391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131704 q = 1) (hb : d181392 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131704, d181392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131704, d181392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d131705 q = 1) (hb : d181393 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131705, d181393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131705, d181393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41015 (p : Pattern) (ha : d131722 p = 1) (hb : d181396 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1868 q = 1) (hb : d53194 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1868, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro209 q ha hb
  have h2 (q : Pattern) (ha : d19313 q = 1) (hb : d131685 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19313, d131685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19313, d131685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d131686 q = 1) (hb : d181378 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131686, d181378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d131686, d181378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d131687 q = 1) (hb : d181379 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131687, d181379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131687, d181379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131688 q = 1) (hb : d181380 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131688, d181380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131688, d181380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131722 q = 1) (hb : d181396 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d131722, d181396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131722, d181396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro41016 (p : Pattern) (ha : d131732 p = 1) (hb : d181402 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131643 q = 1) (hb : d181351 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131643, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41005 q ha hb
    | true =>
      simp only [d131643, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41007 q ha hb
  have h2 (q : Pattern) (ha : d131644 q = 1) (hb : d181352 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131644, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131644, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131645 q = 1) (hb : d181353 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131645, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131645, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131655 q = 1) (hb : d181361 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131655, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41007 q ha hb
    | true =>
      simp only [d131655, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41008 q ha hb
  have h5 (q : Pattern) (ha : d131656 q = 1) (hb : d181362 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131656, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131656, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131657 q = 1) (hb : d181363 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131657, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131657, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131658 q = 1) (hb : d181364 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131658, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131658, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131723 q = 1) (hb : d181397 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131723, d181397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41007 q ha hb
    | true =>
      simp only [d131723, d181397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41015 q ha hb
  have h9 (q : Pattern) (ha : d131724 q = 1) (hb : d181398 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131724, d181398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131724, d181398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d131725 q = 1) (hb : d181399 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131725, d181399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131725, d181399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d131726 q = 1) (hb : d181400 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131726, d181400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d131726, d181400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d131727 q = 1) (hb : d181401 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d131727, d181401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131727, d181401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d131731 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d131732 q = 1) (hb : d181402 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131732, d181402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d131732, d181402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  exact h14 p ha hb
theorem andIntro41017 (p : Pattern) (ha : d131738 p = 1) (hb : d181408 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131733 q = 1) (hb : d181403 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131733, d181403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41016 q ha hb
    | true =>
      simp only [d131733, d181403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131734 q = 1) (hb : d181404 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131734, d181404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131734, d181404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131735 q = 1) (hb : d181405 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131735, d181405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131735, d181405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131736 q = 1) (hb : d181406 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131736, d181406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131736, d181406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131737 q = 1) (hb : d181407 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131737, d181407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131737, d181407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131738 q = 1) (hb : d181408 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131738, d181408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131738, d181408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41018 (p : Pattern) (ha : d131744 p = 1) (hb : d181414 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131706 q = 1) (hb : d181394 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131706, d181394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41011 q ha hb
    | true =>
      simp only [d131706, d181394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41014 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d131720 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131721 q = 1) (hb : d181395 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131721, d181395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131721, d181395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131739 q = 1) (hb : d181409 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131739, d181409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41017 q ha hb
    | true =>
      simp only [d131739, d181409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131740 q = 1) (hb : d181410 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131740, d181410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131740, d181410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131741 q = 1) (hb : d181411 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131741, d181411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131741, d181411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131742 q = 1) (hb : d181412 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131742, d181412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131742, d181412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131743 q = 1) (hb : d181413 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131743, d181413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131743, d181413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d131744 q = 1) (hb : d181414 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131744, d181414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131744, d181414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41019 (p : Pattern) (ha : d131719 p = 1) (hb : d181419 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131700 q = 1) (hb : d181388 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131700, d181388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41013 q ha hb
    | true =>
      simp only [d131700, d181388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131701 q = 1) (hb : d181389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131701, d181389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131701, d181389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131716 q = 1) (hb : d181416 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131716, d181416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131716, d181416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131717 q = 1) (hb : d181417 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131717, d181417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131717, d181417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131718 q = 1) (hb : d181418 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131718, d181418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131718, d181418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131719 q = 1) (hb : d181419 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131719, d181419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131719, d181419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41020 (p : Pattern) (ha : d131751 p = 1) (hb : d181425 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131746 q = 1) (hb : d181420 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131746, d181420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41019 q ha hb
    | true =>
      simp only [d131746, d181420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131747 q = 1) (hb : d181421 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131747, d181421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131747, d181421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131748 q = 1) (hb : d181422 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131748, d181422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131748, d181422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131749 q = 1) (hb : d181423 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131749, d181423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131749, d181423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131750 q = 1) (hb : d181424 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131750, d181424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131750, d181424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131751 q = 1) (hb : d181425 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131751, d181425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131751, d181425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41021 (p : Pattern) (ha : d131757 p = 1) (hb : d181431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131745 q = 1) (hb : d181415 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131745, d181415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131745, d181415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41018 q ha hb
  have h2 (q : Pattern) (ha : d131752 q = 1) (hb : d181426 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131752, d181426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131752, d181426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41020 q ha hb
  have h3 (q : Pattern) (ha : d131753 q = 1) (hb : d181427 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131753, d181427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131753, d181427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131754 q = 1) (hb : d181428 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131754, d181428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131754, d181428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131755 q = 1) (hb : d181429 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131755, d181429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131755, d181429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131756 q = 1) (hb : d181430 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131756, d181430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131756, d181430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131757 q = 1) (hb : d181431 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131757, d181431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131757, d181431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41022 (p : Pattern) (ha : d131763 p = 1) (hb : d181437 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131758 q = 1) (hb : d181432 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131758, d181432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131758, d181432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41021 q ha hb
  have h2 (q : Pattern) (ha : d131759 q = 1) (hb : d181433 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131759, d181433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131759, d181433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131760 q = 1) (hb : d181434 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131760, d181434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131760, d181434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131761 q = 1) (hb : d181435 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131761, d181435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131761, d181435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131762 q = 1) (hb : d181436 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131762, d181436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131762, d181436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131763 q = 1) (hb : d181437 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131763, d181437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131763, d181437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41023 (p : Pattern) (ha : d131779 p = 1) (hb : d181450 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2331 q = 1) (hb : d53496 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2331, d53496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2331, d53496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro289 q ha hb
  have h2 (q : Pattern) (ha : d19462 q = 1) (hb : d131768 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19462, d131768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19462, d131768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53424 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d131769 q = 1) (hb : d181442 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131769, d181442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d131769, d181442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d131770 q = 1) (hb : d181443 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131770, d181443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131770, d181443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d17369 q = 1) (hb : d128031 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17369, d128031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17369, d128031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23366 q ha hb
  have h7 (q : Pattern) (ha : d19465 q = 1) (hb : d131771 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19465, d131771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19465, d131771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d101666 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d131772 q = 1) (hb : d181444 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131772, d181444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d131772, d181444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d131773 q = 1) (hb : d181445 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131773, d181445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d131773, d181445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d131774 q = 1) (hb : d181446 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131774, d181446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131774, d181446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13813 q = 1) (hb : d113965 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
  have h13 (q : Pattern) (ha : d19469 q = 1) (hb : d131775 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19469, d131775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19469, d131775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d101676 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d131776 q = 1) (hb : d181447 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131776, d181447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d131776, d181447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d131777 q = 1) (hb : d181448 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131777, d181448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d131777, d181448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d131778 q = 1) (hb : d181449 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131778, d181449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131778, d181449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d131779 q = 1) (hb : d181450 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d131779, d181450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d131779, d181450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro41024 (p : Pattern) (ha : d131791 p = 1) (hb : d181459 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2335 q = 1) (hb : d53500 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2335, d53500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2335, d53500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro262 q ha hb
  have h2 (q : Pattern) (ha : d19474 q = 1) (hb : d131780 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19474, d131780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19474, d131780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d131781 q = 1) (hb : d181451 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131781, d181451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d131781, d181451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d131782 q = 1) (hb : d181452 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131782, d181452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131782, d181452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d17376 q = 1) (hb : d128038 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17376, d128038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17376, d128038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23369 q ha hb
  have h7 (q : Pattern) (ha : d19477 q = 1) (hb : d131783 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19477, d131783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19477, d131783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d101687 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d131784 q = 1) (hb : d181453 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131784, d181453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d131784, d181453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d131785 q = 1) (hb : d181454 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131785, d181454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d131785, d181454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d131786 q = 1) (hb : d181455 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131786, d181455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131786, d181455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13813 q = 1) (hb : d113965 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
  have h13 (q : Pattern) (ha : d19469 q = 1) (hb : d131775 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19469, d131775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19469, d131775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d101676 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d131776 q = 1) (hb : d181447 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131776, d181447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d131776, d181447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d131777 q = 1) (hb : d181448 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131777, d181448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d131777, d181448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d15775 q = 1) (hb : d123728 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23358 q ha hb
  have h18 (q : Pattern) (ha : d19481 q = 1) (hb : d131787 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19481, d131787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d19481, d131787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d101694 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d131788 q = 1) (hb : d181456 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131788, d181456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d131788, d181456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d131789 q = 1) (hb : d181457 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131789, d181457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d131789, d181457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d131790 q = 1) (hb : d181458 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131790, d181458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d131790, d181458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d131791 q = 1) (hb : d181459 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d131791, d181459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d131791, d181459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro41025 (p : Pattern) (ha : d131796 p = 1) (hb : d181464 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13813 q = 1) (hb : d113965 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
  have h2 (q : Pattern) (ha : d19469 q = 1) (hb : d131775 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19469, d131775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19469, d131775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d101676 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d131776 q = 1) (hb : d181447 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131776, d181447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d131776, d181447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d131777 q = 1) (hb : d181448 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131777, d181448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131777, d181448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d15775 q = 1) (hb : d123728 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23358 q ha hb
  have h7 (q : Pattern) (ha : d19481 q = 1) (hb : d131787 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19481, d131787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19481, d131787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d101694 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d131788 q = 1) (hb : d181456 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131788, d181456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d131788, d181456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d131789 q = 1) (hb : d181457 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131789, d181457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d131789, d181457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d131790 q = 1) (hb : d181458 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131790, d181458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131790, d181458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d131795 q = 1) (hb : d181463 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131795, d181463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d131795, d181463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d131796 q = 1) (hb : d181464 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d131796, d181464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d131796, d181464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro41026 (p : Pattern) (ha : d131808 p = 1) (hb : d181474 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2340 q = 1) (hb : d53505 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2340, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2340, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro267 q ha hb
  have h2 (q : Pattern) (ha : d19495 q = 1) (hb : d131801 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19495, d131801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19495, d131801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d131802 q = 1) (hb : d181469 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131802, d181469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d131802, d181469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d131803 q = 1) (hb : d181470 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131803, d181470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131803, d181470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d17391 q = 1) (hb : d128053 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17391, d128053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17391, d128053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23359 q ha hb
  have h7 (q : Pattern) (ha : d19498 q = 1) (hb : d131804 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19498, d131804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19498, d131804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d101714 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d131805 q = 1) (hb : d181471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131805, d181471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d131805, d181471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d131806 q = 1) (hb : d181472 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131806, d181472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d131806, d181472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d131807 q = 1) (hb : d181473 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131807, d181473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131807, d181473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15775 q = 1) (hb : d123728 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23358 q ha hb
  have h13 (q : Pattern) (ha : d19481 q = 1) (hb : d131787 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19481, d131787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19481, d131787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d101694 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d131788 q = 1) (hb : d181456 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131788, d181456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d131788, d181456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d131789 q = 1) (hb : d181457 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131789, d181457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d131789, d181457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d131795 q = 1) (hb : d181463 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131795, d181463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d131795, d181463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d131808 q = 1) (hb : d181474 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d131808, d181474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d131808, d181474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro41027 (p : Pattern) (ha : d131820 p = 1) (hb : d181484 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6643 q = 1) (hb : d76361 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6643, d76361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6643, d76361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7980 q ha hb
  have h2 (q : Pattern) (ha : d19506 q = 1) (hb : d131812 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19506, d131812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19506, d131812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d69332 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d131813 q = 1) (hb : d181478 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131813, d181478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d131813, d181478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d131814 q = 1) (hb : d181479 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131814, d181479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131814, d181479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131815 q = 1) (hb : d181480 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131815, d181480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131815, d181480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d15790 q = 1) (hb : d123743 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
  have h8 (q : Pattern) (ha : d19510 q = 1) (hb : d131816 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19510, d131816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19510, d131816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d101735 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d131817 q = 1) (hb : d181481 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131817, d181481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d131817, d181481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d131818 q = 1) (hb : d181482 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131818, d181482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d131818, d181482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d131819 q = 1) (hb : d181483 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131819, d181483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d131819, d181483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d131820 q = 1) (hb : d181484 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d131820, d181484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131820, d181484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro41028 (p : Pattern) (ha : d131837 p = 1) (hb : d181490 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131792 q = 1) (hb : d181460 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131792, d181460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41023 q ha hb
    | true =>
      simp only [d131792, d181460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41024 q ha hb
  have h2 (q : Pattern) (ha : d131793 q = 1) (hb : d181461 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131793, d181461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131793, d181461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131794 q = 1) (hb : d181462 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131794, d181462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131794, d181462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131797 q = 1) (hb : d181465 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131797, d181465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41024 q ha hb
    | true =>
      simp only [d131797, d181465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41025 q ha hb
  have h5 (q : Pattern) (ha : d131798 q = 1) (hb : d181466 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131798, d181466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131798, d181466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131799 q = 1) (hb : d181467 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131799, d181467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131799, d181467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131800 q = 1) (hb : d181468 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131800, d181468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131800, d181468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131809 q = 1) (hb : d181475 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131809, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41024 q ha hb
    | true =>
      simp only [d131809, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41026 q ha hb
  have h9 (q : Pattern) (ha : d131810 q = 1) (hb : d181476 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131810, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131810, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d131811 q = 1) (hb : d181477 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131811, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131811, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d131821 q = 1) (hb : d181485 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131821, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41026 q ha hb
    | true =>
      simp only [d131821, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41027 q ha hb
  have h12 (q : Pattern) (ha : d131822 q = 1) (hb : d181486 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131822, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131822, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d131823 q = 1) (hb : d181487 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131823, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131823, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d131824 q = 1) (hb : d181488 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131824, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d131824, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d131825 q = 1) (hb : d181489 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d131825, d181489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131825, d181489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d131836 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d131837 q = 1) (hb : d181490 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131837, d181490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d131837, d181490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro41029 (p : Pattern) (ha : d131844 p = 1) (hb : d181495 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131809 q = 1) (hb : d181475 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131809, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41024 q ha hb
    | true =>
      simp only [d131809, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41026 q ha hb
  have h2 (q : Pattern) (ha : d131810 q = 1) (hb : d181476 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131810, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131810, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131811 q = 1) (hb : d181477 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131811, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131811, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131821 q = 1) (hb : d181485 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131821, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41026 q ha hb
    | true =>
      simp only [d131821, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41027 q ha hb
  have h5 (q : Pattern) (ha : d131822 q = 1) (hb : d181486 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131822, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131822, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131823 q = 1) (hb : d181487 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131823, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131823, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131824 q = 1) (hb : d181488 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131824, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131824, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131840 q = 1) (hb : d181493 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131840, d181493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131840, d181493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d131841 q = 1) (hb : d181494 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d131841, d181494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131841, d181494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d131843 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d131844 q = 1) (hb : d181495 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131844, d181495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d131844, d181495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro41030 (p : Pattern) (ha : d131850 p = 1) (hb : d181501 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131838 q = 1) (hb : d181491 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131838, d181491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41028 q ha hb
    | true =>
      simp only [d131838, d181491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131839 q = 1) (hb : d181492 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131839, d181492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131839, d181492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131845 q = 1) (hb : d181496 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131845, d181496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41029 q ha hb
    | true =>
      simp only [d131845, d181496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131846 q = 1) (hb : d181497 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131846, d181497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131846, d181497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131847 q = 1) (hb : d181498 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131847, d181498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131847, d181498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131848 q = 1) (hb : d181499 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131848, d181499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131848, d181499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131849 q = 1) (hb : d181500 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131849, d181500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131849, d181500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d131850 q = 1) (hb : d181501 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131850, d181501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131850, d181501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41031 (p : Pattern) (ha : d131855 p = 1) (hb : d181505 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2346 q = 1) (hb : d53511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2346, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2346, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro268 q ha hb
  have h2 (q : Pattern) (ha : d19545 q = 1) (hb : d131851 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19545, d131851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19545, d131851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d131852 q = 1) (hb : d181502 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131852, d181502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d131852, d181502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d131853 q = 1) (hb : d181503 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131853, d181503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131853, d181503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131854 q = 1) (hb : d181504 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131854, d181504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131854, d181504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d15790 q = 1) (hb : d123743 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
  have h8 (q : Pattern) (ha : d19510 q = 1) (hb : d131816 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19510, d131816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19510, d131816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d101735 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d131817 q = 1) (hb : d181481 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131817, d181481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d131817, d181481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d131818 q = 1) (hb : d181482 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131818, d181482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d131818, d181482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d131819 q = 1) (hb : d181483 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131819, d181483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d131819, d181483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d131855 q = 1) (hb : d181505 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d131855, d181505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131855, d181505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro41032 (p : Pattern) (ha : d131865 p = 1) (hb : d181511 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131856 q = 1) (hb : d181506 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131856, d181506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41026 q ha hb
    | true =>
      simp only [d131856, d181506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41031 q ha hb
  have h2 (q : Pattern) (ha : d131857 q = 1) (hb : d181507 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131857, d181507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131857, d181507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131858 q = 1) (hb : d181508 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131858, d181508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131858, d181508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131859 q = 1) (hb : d181509 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131859, d181509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131859, d181509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131860 q = 1) (hb : d181510 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d131860, d181510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131860, d181510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d131864 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d131865 q = 1) (hb : d181511 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131865, d181511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131865, d181511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro41033 (p : Pattern) (ha : d131871 p = 1) (hb : d181517 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131845 q = 1) (hb : d181496 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131845, d181496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41029 q ha hb
    | true =>
      simp only [d131845, d181496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131846 q = 1) (hb : d181497 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131846, d181497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131846, d181497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131866 q = 1) (hb : d181512 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131866, d181512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41032 q ha hb
    | true =>
      simp only [d131866, d181512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131867 q = 1) (hb : d181513 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131867, d181513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131867, d181513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131868 q = 1) (hb : d181514 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131868, d181514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131868, d181514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131869 q = 1) (hb : d181515 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131869, d181515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131869, d181515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131870 q = 1) (hb : d181516 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131870, d181516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131870, d181516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d131871 q = 1) (hb : d181517 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131871, d181517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131871, d181517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41034 (p : Pattern) (ha : d131888 p = 1) (hb : d181520 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2346 q = 1) (hb : d53511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2346, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2346, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro268 q ha hb
  have h2 (q : Pattern) (ha : d19545 q = 1) (hb : d131851 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19545, d131851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19545, d131851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d131852 q = 1) (hb : d181502 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d131852, d181502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d131852, d181502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d131853 q = 1) (hb : d181503 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d131853, d181503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131853, d181503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131854 q = 1) (hb : d181504 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d131854, d181504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131854, d181504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131888 q = 1) (hb : d181520 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d131888, d181520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131888, d181520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro41035 (p : Pattern) (ha : d131898 p = 1) (hb : d181526 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131809 q = 1) (hb : d181475 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131809, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41024 q ha hb
    | true =>
      simp only [d131809, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41026 q ha hb
  have h2 (q : Pattern) (ha : d131810 q = 1) (hb : d181476 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131810, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131810, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131811 q = 1) (hb : d181477 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131811, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131811, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131821 q = 1) (hb : d181485 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131821, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41026 q ha hb
    | true =>
      simp only [d131821, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41027 q ha hb
  have h5 (q : Pattern) (ha : d131822 q = 1) (hb : d181486 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131822, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131822, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131823 q = 1) (hb : d181487 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131823, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131823, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131824 q = 1) (hb : d181488 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131824, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131824, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131889 q = 1) (hb : d181521 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131889, d181521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41026 q ha hb
    | true =>
      simp only [d131889, d181521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41034 q ha hb
  have h9 (q : Pattern) (ha : d131890 q = 1) (hb : d181522 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131890, d181522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131890, d181522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d131891 q = 1) (hb : d181523 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131891, d181523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131891, d181523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d131892 q = 1) (hb : d181524 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131892, d181524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d131892, d181524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d131893 q = 1) (hb : d181525 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d131893, d181525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131893, d181525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d131897 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d131898 q = 1) (hb : d181526 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131898, d181526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d131898, d181526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  exact h14 p ha hb
theorem andIntro41036 (p : Pattern) (ha : d131904 p = 1) (hb : d181532 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131899 q = 1) (hb : d181527 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131899, d181527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41035 q ha hb
    | true =>
      simp only [d131899, d181527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131900 q = 1) (hb : d181528 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131900, d181528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131900, d181528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131901 q = 1) (hb : d181529 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131901, d181529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131901, d181529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131902 q = 1) (hb : d181530 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131902, d181530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131902, d181530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131903 q = 1) (hb : d181531 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131903, d181531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131903, d181531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131904 q = 1) (hb : d181532 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131904, d181532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131904, d181532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41037 (p : Pattern) (ha : d131910 p = 1) (hb : d181538 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131872 q = 1) (hb : d181518 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131872, d181518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41030 q ha hb
    | true =>
      simp only [d131872, d181518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41033 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d131886 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131887 q = 1) (hb : d181519 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131887, d181519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131887, d181519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131905 q = 1) (hb : d181533 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131905, d181533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41036 q ha hb
    | true =>
      simp only [d131905, d181533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131906 q = 1) (hb : d181534 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131906, d181534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131906, d181534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131907 q = 1) (hb : d181535 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131907, d181535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131907, d181535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131908 q = 1) (hb : d181536 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131908, d181536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131908, d181536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131909 q = 1) (hb : d181537 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131909, d181537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131909, d181537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d131910 q = 1) (hb : d181538 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131910, d181538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131910, d181538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41038 (p : Pattern) (ha : d131885 p = 1) (hb : d181543 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131866 q = 1) (hb : d181512 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131866, d181512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41032 q ha hb
    | true =>
      simp only [d131866, d181512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131867 q = 1) (hb : d181513 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131867, d181513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131867, d181513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131882 q = 1) (hb : d181540 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131882, d181540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131882, d181540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131883 q = 1) (hb : d181541 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131883, d181541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131883, d181541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131884 q = 1) (hb : d181542 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131884, d181542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131884, d181542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131885 q = 1) (hb : d181543 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131885, d181543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131885, d181543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41039 (p : Pattern) (ha : d131917 p = 1) (hb : d181549 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131912 q = 1) (hb : d181544 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131912, d181544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41038 q ha hb
    | true =>
      simp only [d131912, d181544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131913 q = 1) (hb : d181545 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131913, d181545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131913, d181545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131914 q = 1) (hb : d181546 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131914, d181546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131914, d181546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131915 q = 1) (hb : d181547 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131915, d181547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131915, d181547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131916 q = 1) (hb : d181548 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131916, d181548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131916, d181548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131917 q = 1) (hb : d181549 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131917, d181549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131917, d181549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41040 (p : Pattern) (ha : d131923 p = 1) (hb : d181555 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131911 q = 1) (hb : d181539 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131911, d181539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131911, d181539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41037 q ha hb
  have h2 (q : Pattern) (ha : d131918 q = 1) (hb : d181550 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131918, d181550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131918, d181550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41039 q ha hb
  have h3 (q : Pattern) (ha : d131919 q = 1) (hb : d181551 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131919, d181551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131919, d181551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131920 q = 1) (hb : d181552 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131920, d181552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131920, d181552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131921 q = 1) (hb : d181553 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131921, d181553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131921, d181553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131922 q = 1) (hb : d181554 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131922, d181554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131922, d181554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131923 q = 1) (hb : d181555 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131923, d181555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131923, d181555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41041 (p : Pattern) (ha : d131929 p = 1) (hb : d181561 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131924 q = 1) (hb : d181556 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131924, d181556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131924, d181556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41040 q ha hb
  have h2 (q : Pattern) (ha : d131925 q = 1) (hb : d181557 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131925, d181557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131925, d181557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131926 q = 1) (hb : d181558 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131926, d181558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131926, d181558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131927 q = 1) (hb : d181559 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131927, d181559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131927, d181559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131928 q = 1) (hb : d181560 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131928, d181560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131928, d181560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131929 q = 1) (hb : d181561 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131929, d181561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131929, d181561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41042 (p : Pattern) (ha : d131935 p = 1) (hb : d181567 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d131316 q = 1) (hb : d181096 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131316, d181096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40955 q ha hb
    | true =>
      simp only [d131316, d181096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40968 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d131424 q = 1) (hb : d181185 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131424, d181185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131424, d181185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40984 q ha hb
  have h3 (q : Pattern) (ha : d131425 q = 1) (hb : d181186 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d131425, d181186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131425, d181186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131592 q = 1) (hb : d181310 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131592, d181310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131592, d181310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41003 q ha hb
  have h5 (q : Pattern) (ha : d131593 q = 1) (hb : d181311 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d131593, d181311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131593, d181311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131594 q = 1) (hb : d181312 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d131594, d181312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131594, d181312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131764 q = 1) (hb : d181438 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131764, d181438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131764, d181438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41022 q ha hb
  have h8 (q : Pattern) (ha : d131765 q = 1) (hb : d181439 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d131765, d181439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131765, d181439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d131766 q = 1) (hb : d181440 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d131766, d181440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131766, d181440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d131767 q = 1) (hb : d181441 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d131767, d181441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131767, d181441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d131930 q = 1) (hb : d181562 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131930, d181562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131930, d181562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41041 q ha hb
  have h12 (q : Pattern) (ha : d131931 q = 1) (hb : d181563 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d131931, d181563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131931, d181563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d131932 q = 1) (hb : d181564 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d131932, d181564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131932, d181564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d131933 q = 1) (hb : d181565 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d131933, d181565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131933, d181565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d131934 q = 1) (hb : d181566 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d131934, d181566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d131934, d181566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d131935 q = 1) (hb : d181567 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d131935, d181567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d131935, d181567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro41043 (p : Pattern) (ha : d131941 p = 1) (hb : d181573 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131936 q = 1) (hb : d181568 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d131936, d181568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41042 q ha hb
    | true =>
      simp only [d131936, d181568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131937 q = 1) (hb : d181569 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d131937, d181569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131937, d181569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131938 q = 1) (hb : d181570 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d131938, d181570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131938, d181570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131939 q = 1) (hb : d181571 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d131939, d181571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131939, d181571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131940 q = 1) (hb : d181572 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d131940, d181572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131940, d181572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131941 q = 1) (hb : d181573 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d131941, d181573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131941, d181573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41044 (p : Pattern) (ha : d131947 p = 1) (hb : d181579 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131942 q = 1) (hb : d181574 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d131942, d181574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41043 q ha hb
    | true =>
      simp only [d131942, d181574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131943 q = 1) (hb : d181575 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d131943, d181575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131943, d181575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131944 q = 1) (hb : d181576 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d131944, d181576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131944, d181576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131945 q = 1) (hb : d181577 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d131945, d181577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131945, d181577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131946 q = 1) (hb : d181578 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d131946, d181578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131946, d181578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131947 q = 1) (hb : d181579 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d131947, d181579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131947, d181579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41045 (p : Pattern) (ha : d131953 p = 1) (hb : d181585 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131948 q = 1) (hb : d181580 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d131948, d181580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41044 q ha hb
    | true =>
      simp only [d131948, d181580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131949 q = 1) (hb : d181581 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d131949, d181581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131949, d181581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131950 q = 1) (hb : d181582 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d131950, d181582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131950, d181582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131951 q = 1) (hb : d181583 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d131951, d181583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131951, d181583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131952 q = 1) (hb : d181584 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d131952, d181584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131952, d181584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131953 q = 1) (hb : d181585 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d131953, d181585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131953, d181585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41046 (p : Pattern) (ha : d131959 p = 1) (hb : d181591 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131954 q = 1) (hb : d181586 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d131954, d181586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41045 q ha hb
    | true =>
      simp only [d131954, d181586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131955 q = 1) (hb : d181587 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d131955, d181587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131955, d181587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131956 q = 1) (hb : d181588 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d131956, d181588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131956, d181588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131957 q = 1) (hb : d181589 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d131957, d181589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131957, d181589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131958 q = 1) (hb : d181590 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d131958, d181590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131958, d181590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131959 q = 1) (hb : d181591 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d131959, d181591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131959, d181591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41047 (p : Pattern) (ha : d131965 p = 1) (hb : d181597 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131960 q = 1) (hb : d181592 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d131960, d181592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41046 q ha hb
    | true =>
      simp only [d131960, d181592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131961 q = 1) (hb : d181593 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d131961, d181593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131961, d181593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131962 q = 1) (hb : d181594 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d131962, d181594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131962, d181594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131963 q = 1) (hb : d181595 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d131963, d181595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131963, d181595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131964 q = 1) (hb : d181596 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d131964, d181596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131964, d181596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131965 q = 1) (hb : d181597 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d131965, d181597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131965, d181597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41048 (p : Pattern) (ha : d131971 p = 1) (hb : d181603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131966 q = 1) (hb : d181598 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d131966, d181598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41047 q ha hb
    | true =>
      simp only [d131966, d181598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131967 q = 1) (hb : d181599 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d131967, d181599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131967, d181599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131968 q = 1) (hb : d181600 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d131968, d181600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131968, d181600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131969 q = 1) (hb : d181601 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d131969, d181601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131969, d181601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131970 q = 1) (hb : d181602 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d131970, d181602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131970, d181602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131971 q = 1) (hb : d181603 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d131971, d181603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131971, d181603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41049 (p : Pattern) (ha : d131977 p = 1) (hb : d181609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131972 q = 1) (hb : d181604 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d131972, d181604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41048 q ha hb
    | true =>
      simp only [d131972, d181604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131973 q = 1) (hb : d181605 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d131973, d181605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131973, d181605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131974 q = 1) (hb : d181606 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d131974, d181606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131974, d181606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131975 q = 1) (hb : d181607 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d131975, d181607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131975, d181607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131976 q = 1) (hb : d181608 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d131976, d181608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131976, d181608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131977 q = 1) (hb : d181609 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d131977, d181609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131977, d181609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41050 (p : Pattern) (ha : d61083 p = 1) (hb : d180908 p = 1) : d181614 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17697 q = 1) (hb : d180908 q = 1) : d181011 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17697, d181011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17697, d181011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40836 q ha hb
  have h2 (q : Pattern) (ha : d61079 q = 1) (hb : d180908 q = 1) : d181610 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61079, d181610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61079, d181610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61080 q = 1) (hb : d180908 q = 1) : d181611 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61080, d181611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61080, d181611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61081 q = 1) (hb : d180908 q = 1) : d181612 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61081, d181612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61081, d181612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61082 q = 1) (hb : d180908 q = 1) : d181613 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61082, d181613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61082, d181613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61083 q = 1) (hb : d180908 q = 1) : d181614 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61083, d181614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61083, d181614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41051 (p : Pattern) (ha : d61093 p = 1) (hb : d180908 p = 1) : d181624 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17609 q = 1) (hb : d180908 q = 1) : d180957 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17609, d180957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40833 q ha hb
    | true =>
      simp only [d17609, d180957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40828 q ha hb
  have h2 (q : Pattern) (ha : d61089 q = 1) (hb : d180908 q = 1) : d181620 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d61089, d181620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61089, d181620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61090 q = 1) (hb : d180908 q = 1) : d181621 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d61090, d181621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61090, d181621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61091 q = 1) (hb : d180908 q = 1) : d181622 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d61091, d181622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61091, d181622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61092 q = 1) (hb : d180908 q = 1) : d181623 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d61092, d181623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61092, d181623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61093 q = 1) (hb : d180908 q = 1) : d181624 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d61093, d181624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61093, d181624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41052 (p : Pattern) (ha : d61099 p = 1) (hb : d180908 p = 1) : d181630 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61094 q = 1) (hb : d180908 q = 1) : d181625 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61094, d181625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61094, d181625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41051 q ha hb
  have h2 (q : Pattern) (ha : d61095 q = 1) (hb : d180908 q = 1) : d181626 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61095, d181626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61095, d181626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61096 q = 1) (hb : d180908 q = 1) : d181627 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61096, d181627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61096, d181627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61097 q = 1) (hb : d180908 q = 1) : d181628 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61097, d181628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61097, d181628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61098 q = 1) (hb : d180908 q = 1) : d181629 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61098, d181629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61098, d181629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61099 q = 1) (hb : d180908 q = 1) : d181630 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61099, d181630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61099, d181630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41053 (p : Pattern) (ha : d61105 p = 1) (hb : d180908 p = 1) : d181636 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61084 q = 1) (hb : d180908 q = 1) : d181615 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61084, d181615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61084, d181615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41050 q ha hb
  have h2 (q : Pattern) (ha : d61085 q = 1) (hb : d180908 q = 1) : d181616 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61085, d181616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61085, d181616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61086 q = 1) (hb : d180908 q = 1) : d181617 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61086, d181617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61086, d181617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61087 q = 1) (hb : d180908 q = 1) : d181618 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61087, d181618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61087, d181618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61088 q = 1) (hb : d180908 q = 1) : d181619 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61088, d181619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61088, d181619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61100 q = 1) (hb : d180908 q = 1) : d181631 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61100, d181631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61100, d181631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41052 q ha hb
  have h7 (q : Pattern) (ha : d61101 q = 1) (hb : d180908 q = 1) : d181632 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61101, d181632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61101, d181632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d61102 q = 1) (hb : d180908 q = 1) : d181633 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61102, d181633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61102, d181633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61103 q = 1) (hb : d180908 q = 1) : d181634 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61103, d181634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61103, d181634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61104 q = 1) (hb : d180908 q = 1) : d181635 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61104, d181635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61104, d181635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d61105 q = 1) (hb : d180908 q = 1) : d181636 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61105, d181636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61105, d181636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro41054 (p : Pattern) (ha : d173535 p = 1) (hb : d180908 p = 1) : d181642 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173530 q = 1) (hb : d180908 q = 1) : d181637 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d173530, d181637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40852 q ha hb
    | true =>
      simp only [d173530, d181637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40845 q ha hb
  have h2 (q : Pattern) (ha : d173531 q = 1) (hb : d180908 q = 1) : d181638 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d173531, d181638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173531, d181638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d173532 q = 1) (hb : d180908 q = 1) : d181639 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d173532, d181639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173532, d181639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d173533 q = 1) (hb : d180908 q = 1) : d181640 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d173533, d181640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173533, d181640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173534 q = 1) (hb : d180908 q = 1) : d181641 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d173534, d181641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173534, d181641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173535 q = 1) (hb : d180908 q = 1) : d181642 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d173535, d181642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173535, d181642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41055 (p : Pattern) (ha : d173541 p = 1) (hb : d180908 p = 1) : d181648 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173536 q = 1) (hb : d180908 q = 1) : d181643 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d173536, d181643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173536, d181643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41054 q ha hb
  have h2 (q : Pattern) (ha : d173537 q = 1) (hb : d180908 q = 1) : d181644 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d173537, d181644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173537, d181644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d173538 q = 1) (hb : d180908 q = 1) : d181645 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d173538, d181645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173538, d181645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d173539 q = 1) (hb : d180908 q = 1) : d181646 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d173539, d181646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173539, d181646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d173540 q = 1) (hb : d180908 q = 1) : d181647 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d173540, d181647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173540, d181647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d173541 q = 1) (hb : d180908 q = 1) : d181648 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d173541, d181648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173541, d181648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41056 (p : Pattern) (ha : d173547 p = 1) (hb : d180908 p = 1) : d181654 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173542 q = 1) (hb : d180908 q = 1) : d181649 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d173542, d181649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173542, d181649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41055 q ha hb
  have h2 (q : Pattern) (ha : d173543 q = 1) (hb : d180908 q = 1) : d181650 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d173543, d181650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173543, d181650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d173544 q = 1) (hb : d180908 q = 1) : d181651 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d173544, d181651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173544, d181651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d173545 q = 1) (hb : d180908 q = 1) : d181652 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d173545, d181652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173545, d181652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173546 q = 1) (hb : d180908 q = 1) : d181653 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d173546, d181653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173546, d181653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173547 q = 1) (hb : d180908 q = 1) : d181654 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d173547, d181654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173547, d181654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41057 (p : Pattern) (ha : d173554 p = 1) (hb : d180908 p = 1) : d181661 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173549 q = 1) (hb : d180908 q = 1) : d181656 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d173549, d181656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40868 q ha hb
    | true =>
      simp only [d173549, d181656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40860 q ha hb
  have h2 (q : Pattern) (ha : d173550 q = 1) (hb : d180908 q = 1) : d181657 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d173550, d181657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173550, d181657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d173551 q = 1) (hb : d180908 q = 1) : d181658 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d173551, d181658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173551, d181658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d173552 q = 1) (hb : d180908 q = 1) : d181659 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d173552, d181659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173552, d181659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173553 q = 1) (hb : d180908 q = 1) : d181660 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d173553, d181660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173553, d181660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173554 q = 1) (hb : d180908 q = 1) : d181661 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d173554, d181661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173554, d181661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41058 (p : Pattern) (ha : d173560 p = 1) (hb : d180908 p = 1) : d181667 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173555 q = 1) (hb : d180908 q = 1) : d181662 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d173555, d181662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173555, d181662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41057 q ha hb
  have h2 (q : Pattern) (ha : d173556 q = 1) (hb : d180908 q = 1) : d181663 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d173556, d181663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173556, d181663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d173557 q = 1) (hb : d180908 q = 1) : d181664 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d173557, d181664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173557, d181664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d173558 q = 1) (hb : d180908 q = 1) : d181665 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d173558, d181665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173558, d181665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d173559 q = 1) (hb : d180908 q = 1) : d181666 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d173559, d181666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173559, d181666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d173560 q = 1) (hb : d180908 q = 1) : d181667 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d173560, d181667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173560, d181667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41059 (p : Pattern) (ha : d173566 p = 1) (hb : d180908 p = 1) : d181673 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173561 q = 1) (hb : d180908 q = 1) : d181668 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d173561, d181668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173561, d181668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41058 q ha hb
  have h2 (q : Pattern) (ha : d173562 q = 1) (hb : d180908 q = 1) : d181669 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d173562, d181669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173562, d181669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d173563 q = 1) (hb : d180908 q = 1) : d181670 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d173563, d181670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173563, d181670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d173564 q = 1) (hb : d180908 q = 1) : d181671 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d173564, d181671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173564, d181671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173565 q = 1) (hb : d180908 q = 1) : d181672 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d173565, d181672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173565, d181672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173566 q = 1) (hb : d180908 q = 1) : d181673 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d173566, d181673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173566, d181673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41060 (p : Pattern) (ha : d173570 p = 1) (hb : d180908 p = 1) : d181677 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17980 q = 1) (hb : d180908 q = 1) : d181225 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17980, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40879 q ha hb
    | true =>
      simp only [d17980, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40873 q ha hb
  have h2 (q : Pattern) (ha : d17981 q = 1) (hb : d180908 q = 1) : d181226 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17981, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17981, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17982 q = 1) (hb : d180908 q = 1) : d181227 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17982, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17982, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17990 q = 1) (hb : d180908 q = 1) : d181235 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17990, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40873 q ha hb
    | true =>
      simp only [d17990, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40881 q ha hb
  have h5 (q : Pattern) (ha : d17991 q = 1) (hb : d180908 q = 1) : d181236 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17991, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17991, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17992 q = 1) (hb : d180908 q = 1) : d181237 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17992, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17992, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17993 q = 1) (hb : d180908 q = 1) : d181238 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17993, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17993, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18009 q = 1) (hb : d180908 q = 1) : d181254 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18009, d181254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40873 q ha hb
    | true =>
      simp only [d18009, d181254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40874 q ha hb
  have h9 (q : Pattern) (ha : d18010 q = 1) (hb : d180908 q = 1) : d181255 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18010, d181255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18010, d181255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18011 q = 1) (hb : d180908 q = 1) : d181256 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18011, d181256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18011, d181256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18012 q = 1) (hb : d180908 q = 1) : d181257 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18012, d181257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18012, d181257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d173569 q = 1) (hb : d180908 q = 1) : d181676 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173569, d181676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d173569, d181676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d173570 q = 1) (hb : d180908 q = 1) : d181677 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d173570, d181677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d173570, d181677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro41061 (p : Pattern) (ha : d173576 p = 1) (hb : d180908 p = 1) : d181683 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173571 q = 1) (hb : d180908 q = 1) : d181678 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d173571, d181678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41060 q ha hb
    | true =>
      simp only [d173571, d181678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d173572 q = 1) (hb : d180908 q = 1) : d181679 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d173572, d181679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173572, d181679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18015 q = 1) (hb : d180908 q = 1) : d181260 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18015, d181260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40875 q ha hb
    | true =>
      simp only [d18015, d181260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18016 q = 1) (hb : d180908 q = 1) : d181261 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18016, d181261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18016, d181261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173573 q = 1) (hb : d180908 q = 1) : d181680 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d173573, d181680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173573, d181680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173574 q = 1) (hb : d180908 q = 1) : d181681 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d173574, d181681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173574, d181681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d173575 q = 1) (hb : d180908 q = 1) : d181682 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d173575, d181682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d173575, d181682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d173576 q = 1) (hb : d180908 q = 1) : d181683 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d173576, d181683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d173576, d181683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41062 (p : Pattern) (ha : d173582 p = 1) (hb : d180908 p = 1) : d181689 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173577 q = 1) (hb : d180908 q = 1) : d181684 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d173577, d181684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41061 q ha hb
    | true =>
      simp only [d173577, d181684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40876 q ha hb
  have h2 (q : Pattern) (ha : d173578 q = 1) (hb : d180908 q = 1) : d181685 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d173578, d181685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173578, d181685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d173579 q = 1) (hb : d180908 q = 1) : d181686 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d173579, d181686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173579, d181686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d173580 q = 1) (hb : d180908 q = 1) : d181687 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d173580, d181687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173580, d181687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173581 q = 1) (hb : d180908 q = 1) : d181688 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d173581, d181688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173581, d181688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173582 q = 1) (hb : d180908 q = 1) : d181689 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d173582, d181689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173582, d181689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41063 (p : Pattern) (ha : d173588 p = 1) (hb : d180908 p = 1) : d181695 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173583 q = 1) (hb : d180908 q = 1) : d181690 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d173583, d181690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173583, d181690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41062 q ha hb
  have h2 (q : Pattern) (ha : d173584 q = 1) (hb : d180908 q = 1) : d181691 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d173584, d181691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173584, d181691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d173585 q = 1) (hb : d180908 q = 1) : d181692 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d173585, d181692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173585, d181692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d173586 q = 1) (hb : d180908 q = 1) : d181693 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d173586, d181693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173586, d181693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d173587 q = 1) (hb : d180908 q = 1) : d181694 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d173587, d181694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173587, d181694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d173588 q = 1) (hb : d180908 q = 1) : d181695 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d173588, d181695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173588, d181695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41064 (p : Pattern) (ha : d173594 p = 1) (hb : d180908 p = 1) : d181701 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173589 q = 1) (hb : d180908 q = 1) : d181696 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d173589, d181696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173589, d181696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41063 q ha hb
  have h2 (q : Pattern) (ha : d173590 q = 1) (hb : d180908 q = 1) : d181697 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d173590, d181697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173590, d181697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d173591 q = 1) (hb : d180908 q = 1) : d181698 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d173591, d181698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173591, d181698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d173592 q = 1) (hb : d180908 q = 1) : d181699 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d173592, d181699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173592, d181699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173593 q = 1) (hb : d180908 q = 1) : d181700 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d173593, d181700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173593, d181700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173594 q = 1) (hb : d180908 q = 1) : d181701 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d173594, d181701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173594, d181701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41065 (p : Pattern) (ha : d173599 p = 1) (hb : d180908 p = 1) : d181706 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18161 q = 1) (hb : d180908 q = 1) : d181351 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18161, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40898 q ha hb
    | true =>
      simp only [d18161, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40892 q ha hb
  have h2 (q : Pattern) (ha : d18162 q = 1) (hb : d180908 q = 1) : d181352 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18162, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18162, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18163 q = 1) (hb : d180908 q = 1) : d181353 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18163, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18163, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18171 q = 1) (hb : d180908 q = 1) : d181361 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18171, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40892 q ha hb
    | true =>
      simp only [d18171, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40900 q ha hb
  have h5 (q : Pattern) (ha : d18172 q = 1) (hb : d180908 q = 1) : d181362 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18172, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18172, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18173 q = 1) (hb : d180908 q = 1) : d181363 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18173, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18173, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18174 q = 1) (hb : d180908 q = 1) : d181364 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18174, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18174, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18192 q = 1) (hb : d180908 q = 1) : d181382 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18192, d181382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40892 q ha hb
    | true =>
      simp only [d18192, d181382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40893 q ha hb
  have h9 (q : Pattern) (ha : d18193 q = 1) (hb : d180908 q = 1) : d181383 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18193, d181383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18193, d181383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18194 q = 1) (hb : d180908 q = 1) : d181384 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18194, d181384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18194, d181384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18195 q = 1) (hb : d180908 q = 1) : d181385 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18195, d181385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18195, d181385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d173598 q = 1) (hb : d180908 q = 1) : d181705 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173598, d181705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d173598, d181705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d173599 q = 1) (hb : d180908 q = 1) : d181706 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d173599, d181706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d173599, d181706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro41066 (p : Pattern) (ha : d173605 p = 1) (hb : d180908 p = 1) : d181712 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173600 q = 1) (hb : d180908 q = 1) : d181707 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d173600, d181707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41065 q ha hb
    | true =>
      simp only [d173600, d181707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d173601 q = 1) (hb : d180908 q = 1) : d181708 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d173601, d181708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173601, d181708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18198 q = 1) (hb : d180908 q = 1) : d181388 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18198, d181388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40894 q ha hb
    | true =>
      simp only [d18198, d181388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18199 q = 1) (hb : d180908 q = 1) : d181389 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18199, d181389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18199, d181389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173602 q = 1) (hb : d180908 q = 1) : d181709 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d173602, d181709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173602, d181709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173603 q = 1) (hb : d180908 q = 1) : d181710 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d173603, d181710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173603, d181710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d173604 q = 1) (hb : d180908 q = 1) : d181711 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d173604, d181711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d173604, d181711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d173605 q = 1) (hb : d180908 q = 1) : d181712 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d173605, d181712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d173605, d181712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41067 (p : Pattern) (ha : d173611 p = 1) (hb : d180908 p = 1) : d181718 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173606 q = 1) (hb : d180908 q = 1) : d181713 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d173606, d181713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41066 q ha hb
    | true =>
      simp only [d173606, d181713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40895 q ha hb
  have h2 (q : Pattern) (ha : d173607 q = 1) (hb : d180908 q = 1) : d181714 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d173607, d181714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173607, d181714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d173608 q = 1) (hb : d180908 q = 1) : d181715 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d173608, d181715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173608, d181715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d173609 q = 1) (hb : d180908 q = 1) : d181716 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d173609, d181716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173609, d181716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173610 q = 1) (hb : d180908 q = 1) : d181717 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d173610, d181717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173610, d181717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173611 q = 1) (hb : d180908 q = 1) : d181718 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d173611, d181718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173611, d181718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41068 (p : Pattern) (ha : d173617 p = 1) (hb : d180908 p = 1) : d181724 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173612 q = 1) (hb : d180908 q = 1) : d181719 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d173612, d181719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173612, d181719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41067 q ha hb
  have h2 (q : Pattern) (ha : d173613 q = 1) (hb : d180908 q = 1) : d181720 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d173613, d181720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173613, d181720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d173614 q = 1) (hb : d180908 q = 1) : d181721 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d173614, d181721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173614, d181721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d173615 q = 1) (hb : d180908 q = 1) : d181722 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d173615, d181722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173615, d181722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d173616 q = 1) (hb : d180908 q = 1) : d181723 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d173616, d181723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173616, d181723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d173617 q = 1) (hb : d180908 q = 1) : d181724 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d173617, d181724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173617, d181724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41069 (p : Pattern) (ha : d173623 p = 1) (hb : d180908 p = 1) : d181730 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173618 q = 1) (hb : d180908 q = 1) : d181725 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d173618, d181725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173618, d181725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41068 q ha hb
  have h2 (q : Pattern) (ha : d173619 q = 1) (hb : d180908 q = 1) : d181726 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d173619, d181726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173619, d181726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d173620 q = 1) (hb : d180908 q = 1) : d181727 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d173620, d181727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173620, d181727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d173621 q = 1) (hb : d180908 q = 1) : d181728 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d173621, d181728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173621, d181728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173622 q = 1) (hb : d180908 q = 1) : d181729 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d173622, d181729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173622, d181729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173623 q = 1) (hb : d180908 q = 1) : d181730 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d173623, d181730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173623, d181730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41070 (p : Pattern) (ha : d173629 p = 1) (hb : d180908 p = 1) : d181736 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18342 q = 1) (hb : d180908 q = 1) : d181475 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18342, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40917 q ha hb
    | true =>
      simp only [d18342, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40911 q ha hb
  have h2 (q : Pattern) (ha : d18343 q = 1) (hb : d180908 q = 1) : d181476 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18343, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18343, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18344 q = 1) (hb : d180908 q = 1) : d181477 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18344, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18344, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18352 q = 1) (hb : d180908 q = 1) : d181485 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18352, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40911 q ha hb
    | true =>
      simp only [d18352, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40919 q ha hb
  have h5 (q : Pattern) (ha : d18353 q = 1) (hb : d180908 q = 1) : d181486 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18353, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18353, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18354 q = 1) (hb : d180908 q = 1) : d181487 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18354, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18354, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18355 q = 1) (hb : d180908 q = 1) : d181488 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18355, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18355, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18373 q = 1) (hb : d180908 q = 1) : d181506 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18373, d181506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40911 q ha hb
    | true =>
      simp only [d18373, d181506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40912 q ha hb
  have h9 (q : Pattern) (ha : d18374 q = 1) (hb : d180908 q = 1) : d181507 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18374, d181507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18374, d181507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18375 q = 1) (hb : d180908 q = 1) : d181508 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18375, d181508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18375, d181508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18376 q = 1) (hb : d180908 q = 1) : d181509 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18376, d181509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18376, d181509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d173628 q = 1) (hb : d180908 q = 1) : d181735 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173628, d181735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d173628, d181735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d173629 q = 1) (hb : d180908 q = 1) : d181736 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d173629, d181736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d173629, d181736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro41071 (p : Pattern) (ha : d173635 p = 1) (hb : d180908 p = 1) : d181742 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173630 q = 1) (hb : d180908 q = 1) : d181737 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d173630, d181737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41070 q ha hb
    | true =>
      simp only [d173630, d181737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d173631 q = 1) (hb : d180908 q = 1) : d181738 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d173631, d181738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173631, d181738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18379 q = 1) (hb : d180908 q = 1) : d181512 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18379, d181512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40913 q ha hb
    | true =>
      simp only [d18379, d181512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18380 q = 1) (hb : d180908 q = 1) : d181513 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18380, d181513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18380, d181513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173632 q = 1) (hb : d180908 q = 1) : d181739 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d173632, d181739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173632, d181739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173633 q = 1) (hb : d180908 q = 1) : d181740 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d173633, d181740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173633, d181740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d173634 q = 1) (hb : d180908 q = 1) : d181741 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d173634, d181741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d173634, d181741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d173635 q = 1) (hb : d180908 q = 1) : d181742 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d173635, d181742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d173635, d181742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41072 (p : Pattern) (ha : d173641 p = 1) (hb : d180908 p = 1) : d181748 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173636 q = 1) (hb : d180908 q = 1) : d181743 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d173636, d181743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41071 q ha hb
    | true =>
      simp only [d173636, d181743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40914 q ha hb
  have h2 (q : Pattern) (ha : d173637 q = 1) (hb : d180908 q = 1) : d181744 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d173637, d181744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173637, d181744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d173638 q = 1) (hb : d180908 q = 1) : d181745 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d173638, d181745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173638, d181745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d173639 q = 1) (hb : d180908 q = 1) : d181746 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d173639, d181746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173639, d181746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173640 q = 1) (hb : d180908 q = 1) : d181747 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d173640, d181747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173640, d181747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173641 q = 1) (hb : d180908 q = 1) : d181748 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d173641, d181748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173641, d181748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41073 (p : Pattern) (ha : d173647 p = 1) (hb : d180908 p = 1) : d181754 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173642 q = 1) (hb : d180908 q = 1) : d181749 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d173642, d181749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173642, d181749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41072 q ha hb
  have h2 (q : Pattern) (ha : d173643 q = 1) (hb : d180908 q = 1) : d181750 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d173643, d181750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173643, d181750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d173644 q = 1) (hb : d180908 q = 1) : d181751 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d173644, d181751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173644, d181751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d173645 q = 1) (hb : d180908 q = 1) : d181752 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d173645, d181752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173645, d181752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d173646 q = 1) (hb : d180908 q = 1) : d181753 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d173646, d181753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173646, d181753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d173647 q = 1) (hb : d180908 q = 1) : d181754 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d173647, d181754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173647, d181754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41074 (p : Pattern) (ha : d173653 p = 1) (hb : d180908 p = 1) : d181760 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173648 q = 1) (hb : d180908 q = 1) : d181755 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d173648, d181755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173648, d181755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41073 q ha hb
  have h2 (q : Pattern) (ha : d173649 q = 1) (hb : d180908 q = 1) : d181756 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d173649, d181756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173649, d181756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d173650 q = 1) (hb : d180908 q = 1) : d181757 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d173650, d181757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173650, d181757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d173651 q = 1) (hb : d180908 q = 1) : d181758 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d173651, d181758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173651, d181758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d173652 q = 1) (hb : d180908 q = 1) : d181759 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d173652, d181759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173652, d181759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173653 q = 1) (hb : d180908 q = 1) : d181760 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d173653, d181760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173653, d181760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41075 (p : Pattern) (ha : d173659 p = 1) (hb : d180908 p = 1) : d181766 p = 1 := by
  have h0 (q : Pattern) (ha : d173548 q = 1) (hb : d180908 q = 1) : d181655 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d173548, d181655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41053 q ha hb
    | true =>
      simp only [d173548, d181655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41056 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d173567 q = 1) (hb : d180908 q = 1) : d181674 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d173567, d181674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173567, d181674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41059 q ha hb
  have h3 (q : Pattern) (ha : d173568 q = 1) (hb : d180908 q = 1) : d181675 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d173568, d181675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173568, d181675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d173595 q = 1) (hb : d180908 q = 1) : d181702 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d173595, d181702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173595, d181702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41064 q ha hb
  have h5 (q : Pattern) (ha : d173596 q = 1) (hb : d180908 q = 1) : d181703 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d173596, d181703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173596, d181703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d173597 q = 1) (hb : d180908 q = 1) : d181704 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d173597, d181704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173597, d181704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d173624 q = 1) (hb : d180908 q = 1) : d181731 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d173624, d181731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173624, d181731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41069 q ha hb
  have h8 (q : Pattern) (ha : d173625 q = 1) (hb : d180908 q = 1) : d181732 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d173625, d181732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173625, d181732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d173626 q = 1) (hb : d180908 q = 1) : d181733 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d173626, d181733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173626, d181733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d173627 q = 1) (hb : d180908 q = 1) : d181734 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d173627, d181734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d173627, d181734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d173654 q = 1) (hb : d180908 q = 1) : d181761 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d173654, d181761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173654, d181761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41074 q ha hb
  have h12 (q : Pattern) (ha : d173655 q = 1) (hb : d180908 q = 1) : d181762 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d173655, d181762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173655, d181762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d173656 q = 1) (hb : d180908 q = 1) : d181763 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d173656, d181763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173656, d181763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d173657 q = 1) (hb : d180908 q = 1) : d181764 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d173657, d181764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173657, d181764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d173658 q = 1) (hb : d180908 q = 1) : d181765 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d173658, d181765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d173658, d181765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d173659 q = 1) (hb : d180908 q = 1) : d181766 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d173659, d181766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d173659, d181766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro41076 (p : Pattern) (ha : d173665 p = 1) (hb : d180908 p = 1) : d181772 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173660 q = 1) (hb : d180908 q = 1) : d181767 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d173660, d181767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41075 q ha hb
    | true =>
      simp only [d173660, d181767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d173661 q = 1) (hb : d180908 q = 1) : d181768 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d173661, d181768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173661, d181768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d173662 q = 1) (hb : d180908 q = 1) : d181769 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d173662, d181769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173662, d181769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d173663 q = 1) (hb : d180908 q = 1) : d181770 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d173663, d181770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173663, d181770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d173664 q = 1) (hb : d180908 q = 1) : d181771 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d173664, d181771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173664, d181771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d173665 q = 1) (hb : d180908 q = 1) : d181772 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d173665, d181772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173665, d181772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41077 (p : Pattern) (ha : d173671 p = 1) (hb : d180908 p = 1) : d181778 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173666 q = 1) (hb : d180908 q = 1) : d181773 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d173666, d181773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41076 q ha hb
    | true =>
      simp only [d173666, d181773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d173667 q = 1) (hb : d180908 q = 1) : d181774 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d173667, d181774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173667, d181774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d173668 q = 1) (hb : d180908 q = 1) : d181775 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d173668, d181775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173668, d181775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d173669 q = 1) (hb : d180908 q = 1) : d181776 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d173669, d181776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173669, d181776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d173670 q = 1) (hb : d180908 q = 1) : d181777 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d173670, d181777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173670, d181777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d173671 q = 1) (hb : d180908 q = 1) : d181778 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d173671, d181778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173671, d181778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41078 (p : Pattern) (ha : d173677 p = 1) (hb : d180908 p = 1) : d181784 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173672 q = 1) (hb : d180908 q = 1) : d181779 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d173672, d181779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41077 q ha hb
    | true =>
      simp only [d173672, d181779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d173673 q = 1) (hb : d180908 q = 1) : d181780 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d173673, d181780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173673, d181780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d173674 q = 1) (hb : d180908 q = 1) : d181781 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d173674, d181781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173674, d181781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d173675 q = 1) (hb : d180908 q = 1) : d181782 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d173675, d181782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173675, d181782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d173676 q = 1) (hb : d180908 q = 1) : d181783 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d173676, d181783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173676, d181783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d173677 q = 1) (hb : d180908 q = 1) : d181784 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d173677, d181784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173677, d181784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41079 (p : Pattern) (ha : d173683 p = 1) (hb : d180908 p = 1) : d181790 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173678 q = 1) (hb : d180908 q = 1) : d181785 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d173678, d181785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41078 q ha hb
    | true =>
      simp only [d173678, d181785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d173679 q = 1) (hb : d180908 q = 1) : d181786 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d173679, d181786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173679, d181786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d173680 q = 1) (hb : d180908 q = 1) : d181787 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d173680, d181787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173680, d181787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d173681 q = 1) (hb : d180908 q = 1) : d181788 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d173681, d181788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173681, d181788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d173682 q = 1) (hb : d180908 q = 1) : d181789 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d173682, d181789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173682, d181789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d173683 q = 1) (hb : d180908 q = 1) : d181790 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d173683, d181790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173683, d181790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41080 (p : Pattern) (ha : d173689 p = 1) (hb : d180908 p = 1) : d181796 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173684 q = 1) (hb : d180908 q = 1) : d181791 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d173684, d181791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41079 q ha hb
    | true =>
      simp only [d173684, d181791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d173685 q = 1) (hb : d180908 q = 1) : d181792 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d173685, d181792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173685, d181792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d173686 q = 1) (hb : d180908 q = 1) : d181793 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d173686, d181793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173686, d181793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d173687 q = 1) (hb : d180908 q = 1) : d181794 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d173687, d181794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173687, d181794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d173688 q = 1) (hb : d180908 q = 1) : d181795 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d173688, d181795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173688, d181795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d173689 q = 1) (hb : d180908 q = 1) : d181796 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d173689, d181796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173689, d181796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41081 (p : Pattern) (ha : d173695 p = 1) (hb : d180908 p = 1) : d181802 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173690 q = 1) (hb : d180908 q = 1) : d181797 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d173690, d181797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41080 q ha hb
    | true =>
      simp only [d173690, d181797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d173691 q = 1) (hb : d180908 q = 1) : d181798 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d173691, d181798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173691, d181798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d173692 q = 1) (hb : d180908 q = 1) : d181799 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d173692, d181799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173692, d181799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d173693 q = 1) (hb : d180908 q = 1) : d181800 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d173693, d181800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173693, d181800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d173694 q = 1) (hb : d180908 q = 1) : d181801 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d173694, d181801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173694, d181801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d173695 q = 1) (hb : d180908 q = 1) : d181802 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d173695, d181802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173695, d181802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41082 (p : Pattern) (ha : d173701 p = 1) (hb : d180908 p = 1) : d181808 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d173696 q = 1) (hb : d180908 q = 1) : d181803 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d173696, d181803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41081 q ha hb
    | true =>
      simp only [d173696, d181803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d173697 q = 1) (hb : d180908 q = 1) : d181804 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d173697, d181804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173697, d181804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d173698 q = 1) (hb : d180908 q = 1) : d181805 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d173698, d181805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173698, d181805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d173699 q = 1) (hb : d180908 q = 1) : d181806 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d173699, d181806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173699, d181806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d173700 q = 1) (hb : d180908 q = 1) : d181807 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d173700, d181807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173700, d181807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d173701 q = 1) (hb : d180908 q = 1) : d181808 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d173701, d181808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173701, d181808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41083 (p : Pattern) (ha : d131163 p = 1) (hb : d181010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131158 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d131121 q = 1) (hb : d180925 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131121, d180925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40940 q ha hb
    | true =>
      simp only [d131121, d180925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131159 q = 1) (hb : d181006 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131159, d181006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131159, d181006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d131122 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d131160 q = 1) (hb : d181007 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131160, d181007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131160, d181007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d131161 q = 1) (hb : d181008 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131161, d181008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131161, d181008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131162 q = 1) (hb : d181009 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131162, d181009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131162, d181009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131163 q = 1) (hb : d181010 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131163, d181010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131163, d181010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41084 (p : Pattern) (ha : d131169 p = 1) (hb : d181614 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131164 q = 1) (hb : d181011 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131164, d181011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131164, d181011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41083 q ha hb
  have h2 (q : Pattern) (ha : d131165 q = 1) (hb : d181610 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131165, d181610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131165, d181610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131166 q = 1) (hb : d181611 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131166, d181611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131166, d181611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131167 q = 1) (hb : d181612 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131167, d181612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131167, d181612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131168 q = 1) (hb : d181613 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131168, d181613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131168, d181613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131169 q = 1) (hb : d181614 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131169, d181614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131169, d181614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41085 (p : Pattern) (ha : d131211 p = 1) (hb : d181624 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131200 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d131158 q = 1) (hb : d180957 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131158, d180957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40945 q ha hb
    | true =>
      simp only [d131158, d180957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40940 q ha hb
  have h3 (q : Pattern) (ha : d131201 q = 1) (hb : d181620 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131201, d181620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131201, d181620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d131207 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d131208 q = 1) (hb : d181621 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131208, d181621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131208, d181621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d131209 q = 1) (hb : d181622 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131209, d181622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131209, d181622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131210 q = 1) (hb : d181623 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131210, d181623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131210, d181623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131211 q = 1) (hb : d181624 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131211, d181624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131211, d181624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41086 (p : Pattern) (ha : d131223 p = 1) (hb : d181630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131212 q = 1) (hb : d181625 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131212, d181625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131212, d181625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41085 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d131218 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131219 q = 1) (hb : d181626 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131219, d181626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131219, d181626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131220 q = 1) (hb : d181627 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131220, d181627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131220, d181627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131221 q = 1) (hb : d181628 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131221, d181628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131221, d181628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131222 q = 1) (hb : d181629 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131222, d181629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131222, d181629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131223 q = 1) (hb : d181630 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131223, d181630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131223, d181630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41087 (p : Pattern) (ha : d131229 p = 1) (hb : d181636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131136 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d131170 q = 1) (hb : d181615 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131170, d181615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131170, d181615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41084 q ha hb
  have h3 (q : Pattern) (ha : d131171 q = 1) (hb : d181616 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131171, d181616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131171, d181616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131172 q = 1) (hb : d181617 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131172, d181617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131172, d181617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131173 q = 1) (hb : d181618 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131173, d181618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131173, d181618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131174 q = 1) (hb : d181619 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131174, d181619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131174, d181619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131224 q = 1) (hb : d181631 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131224, d181631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131224, d181631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41086 q ha hb
  have h8 (q : Pattern) (ha : d131225 q = 1) (hb : d181632 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131225, d181632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131225, d181632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d131226 q = 1) (hb : d181633 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131226, d181633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131226, d181633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d131227 q = 1) (hb : d181634 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131227, d181634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131227, d181634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d131228 q = 1) (hb : d181635 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131228, d181635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131228, d181635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d131229 q = 1) (hb : d181636 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131229, d181636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131229, d181636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro41088 (p : Pattern) (ha : d131296 p = 1) (hb : d181642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131280 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d131285 q = 1) (hb : d181637 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131285, d181637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40962 q ha hb
    | true =>
      simp only [d131285, d181637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40965 q ha hb
  have h3 (q : Pattern) (ha : d131286 q = 1) (hb : d181638 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131286, d181638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131286, d181638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d131292 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d131293 q = 1) (hb : d181639 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131293, d181639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131293, d181639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d131294 q = 1) (hb : d181640 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131294, d181640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131294, d181640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131295 q = 1) (hb : d181641 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131295, d181641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131295, d181641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131296 q = 1) (hb : d181642 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131296, d181642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131296, d181642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41089 (p : Pattern) (ha : d131309 p = 1) (hb : d181648 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131297 q = 1) (hb : d181643 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131297, d181643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131297, d181643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41088 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d131304 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131305 q = 1) (hb : d181644 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131305, d181644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131305, d181644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131306 q = 1) (hb : d181645 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131306, d181645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131306, d181645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131307 q = 1) (hb : d181646 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131307, d181646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131307, d181646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131308 q = 1) (hb : d181647 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131308, d181647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131308, d181647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131309 q = 1) (hb : d181648 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131309, d181648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131309, d181648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41090 (p : Pattern) (ha : d131315 p = 1) (hb : d181654 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131310 q = 1) (hb : d181649 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131310, d181649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131310, d181649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41089 q ha hb
  have h2 (q : Pattern) (ha : d131311 q = 1) (hb : d181650 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131311, d181650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131311, d181650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131312 q = 1) (hb : d181651 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131312, d181651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131312, d181651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131313 q = 1) (hb : d181652 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131313, d181652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131313, d181652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131314 q = 1) (hb : d181653 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131314, d181653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131314, d181653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131315 q = 1) (hb : d181654 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131315, d181654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131315, d181654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41091 (p : Pattern) (ha : d131404 p = 1) (hb : d181661 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131388 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d131393 q = 1) (hb : d181656 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131393, d181656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40978 q ha hb
    | true =>
      simp only [d131393, d181656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40981 q ha hb
  have h3 (q : Pattern) (ha : d131394 q = 1) (hb : d181657 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131394, d181657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131394, d181657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d131400 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d131401 q = 1) (hb : d181658 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131401, d181658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131401, d181658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d131402 q = 1) (hb : d181659 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131402, d181659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131402, d181659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131403 q = 1) (hb : d181660 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131403, d181660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131403, d181660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131404 q = 1) (hb : d181661 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131404, d181661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131404, d181661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41092 (p : Pattern) (ha : d131417 p = 1) (hb : d181667 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131405 q = 1) (hb : d181662 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131405, d181662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131405, d181662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41091 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d131412 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131413 q = 1) (hb : d181663 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131413, d181663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131413, d181663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131414 q = 1) (hb : d181664 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131414, d181664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131414, d181664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131415 q = 1) (hb : d181665 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131415, d181665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131415, d181665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131416 q = 1) (hb : d181666 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131416, d181666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131416, d181666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131417 q = 1) (hb : d181667 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131417, d181667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131417, d181667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41093 (p : Pattern) (ha : d131423 p = 1) (hb : d181673 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131418 q = 1) (hb : d181668 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131418, d181668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131418, d181668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41092 q ha hb
  have h2 (q : Pattern) (ha : d131419 q = 1) (hb : d181669 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131419, d181669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131419, d181669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131420 q = 1) (hb : d181670 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131420, d181670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131420, d181670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131421 q = 1) (hb : d181671 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131421, d181671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131421, d181671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131422 q = 1) (hb : d181672 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131422, d181672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131422, d181672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131423 q = 1) (hb : d181673 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131423, d181673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131423, d181673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41094 (p : Pattern) (ha : d131537 p = 1) (hb : d181677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131474 q = 1) (hb : d181225 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131474, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40986 q ha hb
    | true =>
      simp only [d131474, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40988 q ha hb
  have h2 (q : Pattern) (ha : d131475 q = 1) (hb : d181226 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131475, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131475, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131476 q = 1) (hb : d181227 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131476, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131476, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131486 q = 1) (hb : d181235 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131486, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40988 q ha hb
    | true =>
      simp only [d131486, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40989 q ha hb
  have h5 (q : Pattern) (ha : d131487 q = 1) (hb : d181236 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131487, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131487, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131488 q = 1) (hb : d181237 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131488, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131488, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131489 q = 1) (hb : d181238 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131489, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131489, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131518 q = 1) (hb : d181254 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131518, d181254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40988 q ha hb
    | true =>
      simp only [d131518, d181254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40993 q ha hb
  have h9 (q : Pattern) (ha : d131519 q = 1) (hb : d181255 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131519, d181255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131519, d181255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d131520 q = 1) (hb : d181256 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131520, d181256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131520, d181256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d131521 q = 1) (hb : d181257 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131521, d181257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d131521, d181257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d131535 q = 1) (hb : d181676 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d131535, d181676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131535, d181676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d131536 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d131537 q = 1) (hb : d181677 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131537, d181677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d131537, d181677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  exact h14 p ha hb
theorem andIntro41095 (p : Pattern) (ha : d131543 p = 1) (hb : d181683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131538 q = 1) (hb : d181678 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131538, d181678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41094 q ha hb
    | true =>
      simp only [d131538, d181678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131539 q = 1) (hb : d181679 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131539, d181679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131539, d181679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131528 q = 1) (hb : d181260 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131528, d181260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40994 q ha hb
    | true =>
      simp only [d131528, d181260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131529 q = 1) (hb : d181261 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131529, d181261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131529, d181261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131540 q = 1) (hb : d181680 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131540, d181680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131540, d181680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131541 q = 1) (hb : d181681 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131541, d181681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131541, d181681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131542 q = 1) (hb : d181682 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131542, d181682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131542, d181682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d131543 q = 1) (hb : d181683 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131543, d181683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131543, d181683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41096 (p : Pattern) (ha : d131572 p = 1) (hb : d181689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131534 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d131548 q = 1) (hb : d181684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131548, d181684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41095 q ha hb
    | true =>
      simp only [d131548, d181684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41000 q ha hb
  have h3 (q : Pattern) (ha : d131549 q = 1) (hb : d181685 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131549, d181685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131549, d181685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d131568 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d131569 q = 1) (hb : d181686 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131569, d181686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131569, d181686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d131570 q = 1) (hb : d181687 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131570, d181687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131570, d181687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131571 q = 1) (hb : d181688 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131571, d181688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131571, d181688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131572 q = 1) (hb : d181689 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131572, d181689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131572, d181689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41097 (p : Pattern) (ha : d131585 p = 1) (hb : d181695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131573 q = 1) (hb : d181690 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131573, d181690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131573, d181690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41096 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d131580 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131581 q = 1) (hb : d181691 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131581, d181691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131581, d181691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131582 q = 1) (hb : d181692 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131582, d181692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131582, d181692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131583 q = 1) (hb : d181693 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131583, d181693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131583, d181693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131584 q = 1) (hb : d181694 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131584, d181694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131584, d181694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131585 q = 1) (hb : d181695 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131585, d181695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131585, d181695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41098 (p : Pattern) (ha : d131591 p = 1) (hb : d181701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131586 q = 1) (hb : d181696 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131586, d181696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131586, d181696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41097 q ha hb
  have h2 (q : Pattern) (ha : d131587 q = 1) (hb : d181697 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131587, d181697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131587, d181697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131588 q = 1) (hb : d181698 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131588, d181698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131588, d181698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131589 q = 1) (hb : d181699 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131589, d181699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131589, d181699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131590 q = 1) (hb : d181700 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131590, d181700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131590, d181700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131591 q = 1) (hb : d181701 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131591, d181701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131591, d181701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41099 (p : Pattern) (ha : d131709 p = 1) (hb : d181706 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131643 q = 1) (hb : d181351 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131643, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41005 q ha hb
    | true =>
      simp only [d131643, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41007 q ha hb
  have h2 (q : Pattern) (ha : d131644 q = 1) (hb : d181352 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131644, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131644, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131645 q = 1) (hb : d181353 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131645, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131645, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131655 q = 1) (hb : d181361 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131655, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41007 q ha hb
    | true =>
      simp only [d131655, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41008 q ha hb
  have h5 (q : Pattern) (ha : d131656 q = 1) (hb : d181362 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131656, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131656, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131657 q = 1) (hb : d181363 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131657, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131657, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131658 q = 1) (hb : d181364 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131658, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131658, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131690 q = 1) (hb : d181382 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131690, d181382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41007 q ha hb
    | true =>
      simp only [d131690, d181382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41012 q ha hb
  have h9 (q : Pattern) (ha : d131691 q = 1) (hb : d181383 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131691, d181383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131691, d181383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d131692 q = 1) (hb : d181384 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131692, d181384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131692, d181384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d131693 q = 1) (hb : d181385 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131693, d181385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d131693, d181385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d131707 q = 1) (hb : d181705 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d131707, d181705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131707, d181705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d131708 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d131709 q = 1) (hb : d181706 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131709, d181706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d131709, d181706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  exact h14 p ha hb
theorem andIntro41100 (p : Pattern) (ha : d131715 p = 1) (hb : d181712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131710 q = 1) (hb : d181707 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131710, d181707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41099 q ha hb
    | true =>
      simp only [d131710, d181707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131711 q = 1) (hb : d181708 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131711, d181708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131711, d181708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131700 q = 1) (hb : d181388 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131700, d181388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41013 q ha hb
    | true =>
      simp only [d131700, d181388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131701 q = 1) (hb : d181389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131701, d181389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131701, d181389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131712 q = 1) (hb : d181709 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131712, d181709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131712, d181709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131713 q = 1) (hb : d181710 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131713, d181710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131713, d181710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131714 q = 1) (hb : d181711 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131714, d181711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131714, d181711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d131715 q = 1) (hb : d181712 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131715, d181712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131715, d181712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41101 (p : Pattern) (ha : d131744 p = 1) (hb : d181718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131706 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d131720 q = 1) (hb : d181713 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131720, d181713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41100 q ha hb
    | true =>
      simp only [d131720, d181713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41019 q ha hb
  have h3 (q : Pattern) (ha : d131721 q = 1) (hb : d181714 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131721, d181714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131721, d181714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d131740 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d131741 q = 1) (hb : d181715 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131741, d181715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131741, d181715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d131742 q = 1) (hb : d181716 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131742, d181716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131742, d181716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131743 q = 1) (hb : d181717 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131743, d181717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131743, d181717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131744 q = 1) (hb : d181718 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131744, d181718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131744, d181718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41102 (p : Pattern) (ha : d131757 p = 1) (hb : d181724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131745 q = 1) (hb : d181719 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131745, d181719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131745, d181719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41101 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d131752 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131753 q = 1) (hb : d181720 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131753, d181720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131753, d181720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131754 q = 1) (hb : d181721 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131754, d181721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131754, d181721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131755 q = 1) (hb : d181722 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131755, d181722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131755, d181722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131756 q = 1) (hb : d181723 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131756, d181723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131756, d181723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131757 q = 1) (hb : d181724 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131757, d181724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131757, d181724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41103 (p : Pattern) (ha : d131763 p = 1) (hb : d181730 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131758 q = 1) (hb : d181725 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131758, d181725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131758, d181725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41102 q ha hb
  have h2 (q : Pattern) (ha : d131759 q = 1) (hb : d181726 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131759, d181726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131759, d181726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131760 q = 1) (hb : d181727 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131760, d181727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131760, d181727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131761 q = 1) (hb : d181728 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131761, d181728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131761, d181728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131762 q = 1) (hb : d181729 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131762, d181729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131762, d181729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131763 q = 1) (hb : d181730 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131763, d181730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131763, d181730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41104 (p : Pattern) (ha : d131875 p = 1) (hb : d181736 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131809 q = 1) (hb : d181475 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131809, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41024 q ha hb
    | true =>
      simp only [d131809, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41026 q ha hb
  have h2 (q : Pattern) (ha : d131810 q = 1) (hb : d181476 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131810, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131810, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131811 q = 1) (hb : d181477 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131811, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131811, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131821 q = 1) (hb : d181485 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131821, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41026 q ha hb
    | true =>
      simp only [d131821, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41027 q ha hb
  have h5 (q : Pattern) (ha : d131822 q = 1) (hb : d181486 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131822, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131822, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131823 q = 1) (hb : d181487 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131823, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131823, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131824 q = 1) (hb : d181488 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131824, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131824, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131856 q = 1) (hb : d181506 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d131856, d181506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41026 q ha hb
    | true =>
      simp only [d131856, d181506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41031 q ha hb
  have h9 (q : Pattern) (ha : d131857 q = 1) (hb : d181507 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d131857, d181507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131857, d181507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d131858 q = 1) (hb : d181508 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d131858, d181508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131858, d181508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d131859 q = 1) (hb : d181509 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d131859, d181509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d131859, d181509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d131873 q = 1) (hb : d181735 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d131873, d181735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131873, d181735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d131874 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d131875 q = 1) (hb : d181736 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d131875, d181736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d131875, d181736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  exact h14 p ha hb
theorem andIntro41105 (p : Pattern) (ha : d131881 p = 1) (hb : d181742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131876 q = 1) (hb : d181737 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131876, d181737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41104 q ha hb
    | true =>
      simp only [d131876, d181737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131877 q = 1) (hb : d181738 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131877, d181738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131877, d181738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131866 q = 1) (hb : d181512 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d131866, d181512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41032 q ha hb
    | true =>
      simp only [d131866, d181512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131867 q = 1) (hb : d181513 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d131867, d181513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131867, d181513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131878 q = 1) (hb : d181739 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d131878, d181739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131878, d181739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131879 q = 1) (hb : d181740 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d131879, d181740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131879, d181740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131880 q = 1) (hb : d181741 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d131880, d181741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131880, d181741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d131881 q = 1) (hb : d181742 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d131881, d181742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131881, d181742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41106 (p : Pattern) (ha : d131910 p = 1) (hb : d181748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131872 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d131886 q = 1) (hb : d181743 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d131886, d181743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41105 q ha hb
    | true =>
      simp only [d131886, d181743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41038 q ha hb
  have h3 (q : Pattern) (ha : d131887 q = 1) (hb : d181744 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131887, d181744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131887, d181744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d131906 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d131907 q = 1) (hb : d181745 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131907, d181745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131907, d181745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d131908 q = 1) (hb : d181746 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131908, d181746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131908, d181746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131909 q = 1) (hb : d181747 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131909, d181747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131909, d181747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131910 q = 1) (hb : d181748 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131910, d181748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131910, d181748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41107 (p : Pattern) (ha : d131923 p = 1) (hb : d181754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131911 q = 1) (hb : d181749 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131911, d181749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131911, d181749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41106 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d131918 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131919 q = 1) (hb : d181750 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131919, d181750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131919, d181750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131920 q = 1) (hb : d181751 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131920, d181751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131920, d181751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131921 q = 1) (hb : d181752 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131921, d181752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131921, d181752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131922 q = 1) (hb : d181753 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131922, d181753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131922, d181753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131923 q = 1) (hb : d181754 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131923, d181754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131923, d181754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41108 (p : Pattern) (ha : d131929 p = 1) (hb : d181760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131924 q = 1) (hb : d181755 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131924, d181755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131924, d181755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41107 q ha hb
  have h2 (q : Pattern) (ha : d131925 q = 1) (hb : d181756 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131925, d181756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131925, d181756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131926 q = 1) (hb : d181757 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131926, d181757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131926, d181757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131927 q = 1) (hb : d181758 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131927, d181758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131927, d181758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131928 q = 1) (hb : d181759 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131928, d181759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131928, d181759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131929 q = 1) (hb : d181760 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131929, d181760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131929, d181760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41109 (p : Pattern) (ha : d131935 p = 1) (hb : d181766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d131316 q = 1) (hb : d181655 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131316, d181655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41087 q ha hb
    | true =>
      simp only [d131316, d181655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41090 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d131424 q = 1) (hb : d181674 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131424, d181674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131424, d181674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41093 q ha hb
  have h3 (q : Pattern) (ha : d131425 q = 1) (hb : d181675 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d131425, d181675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131425, d181675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131592 q = 1) (hb : d181702 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131592, d181702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131592, d181702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41098 q ha hb
  have h5 (q : Pattern) (ha : d131593 q = 1) (hb : d181703 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d131593, d181703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131593, d181703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131594 q = 1) (hb : d181704 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d131594, d181704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131594, d181704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131764 q = 1) (hb : d181731 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131764, d181731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131764, d181731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41103 q ha hb
  have h8 (q : Pattern) (ha : d131765 q = 1) (hb : d181732 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d131765, d181732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131765, d181732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d131766 q = 1) (hb : d181733 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d131766, d181733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131766, d181733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d131767 q = 1) (hb : d181734 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d131767, d181734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131767, d181734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d131930 q = 1) (hb : d181761 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131930, d181761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131930, d181761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41108 q ha hb
  have h12 (q : Pattern) (ha : d131931 q = 1) (hb : d181762 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d131931, d181762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131931, d181762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d131932 q = 1) (hb : d181763 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d131932, d181763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131932, d181763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d131933 q = 1) (hb : d181764 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d131933, d181764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131933, d181764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d131934 q = 1) (hb : d181765 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d131934, d181765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d131934, d181765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d131935 q = 1) (hb : d181766 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d131935, d181766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d131935, d181766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro41110 (p : Pattern) (ha : d131941 p = 1) (hb : d181772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131936 q = 1) (hb : d181767 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d131936, d181767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41109 q ha hb
    | true =>
      simp only [d131936, d181767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131937 q = 1) (hb : d181768 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d131937, d181768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131937, d181768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131938 q = 1) (hb : d181769 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d131938, d181769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131938, d181769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131939 q = 1) (hb : d181770 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d131939, d181770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131939, d181770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131940 q = 1) (hb : d181771 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d131940, d181771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131940, d181771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131941 q = 1) (hb : d181772 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d131941, d181772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131941, d181772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41111 (p : Pattern) (ha : d131947 p = 1) (hb : d181778 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131942 q = 1) (hb : d181773 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d131942, d181773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41110 q ha hb
    | true =>
      simp only [d131942, d181773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131943 q = 1) (hb : d181774 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d131943, d181774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131943, d181774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131944 q = 1) (hb : d181775 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d131944, d181775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131944, d181775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131945 q = 1) (hb : d181776 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d131945, d181776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131945, d181776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131946 q = 1) (hb : d181777 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d131946, d181777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131946, d181777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131947 q = 1) (hb : d181778 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d131947, d181778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131947, d181778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41112 (p : Pattern) (ha : d131953 p = 1) (hb : d181784 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131948 q = 1) (hb : d181779 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d131948, d181779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41111 q ha hb
    | true =>
      simp only [d131948, d181779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131949 q = 1) (hb : d181780 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d131949, d181780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131949, d181780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131950 q = 1) (hb : d181781 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d131950, d181781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131950, d181781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131951 q = 1) (hb : d181782 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d131951, d181782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131951, d181782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131952 q = 1) (hb : d181783 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d131952, d181783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131952, d181783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131953 q = 1) (hb : d181784 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d131953, d181784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131953, d181784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41113 (p : Pattern) (ha : d131959 p = 1) (hb : d181790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131954 q = 1) (hb : d181785 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d131954, d181785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41112 q ha hb
    | true =>
      simp only [d131954, d181785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131955 q = 1) (hb : d181786 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d131955, d181786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131955, d181786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131956 q = 1) (hb : d181787 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d131956, d181787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131956, d181787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131957 q = 1) (hb : d181788 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d131957, d181788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131957, d181788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131958 q = 1) (hb : d181789 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d131958, d181789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131958, d181789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131959 q = 1) (hb : d181790 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d131959, d181790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131959, d181790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41114 (p : Pattern) (ha : d131965 p = 1) (hb : d181796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131960 q = 1) (hb : d181791 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d131960, d181791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41113 q ha hb
    | true =>
      simp only [d131960, d181791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131961 q = 1) (hb : d181792 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d131961, d181792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131961, d181792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131962 q = 1) (hb : d181793 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d131962, d181793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131962, d181793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131963 q = 1) (hb : d181794 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d131963, d181794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131963, d181794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131964 q = 1) (hb : d181795 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d131964, d181795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131964, d181795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131965 q = 1) (hb : d181796 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d131965, d181796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131965, d181796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41115 (p : Pattern) (ha : d131971 p = 1) (hb : d181802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131966 q = 1) (hb : d181797 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d131966, d181797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41114 q ha hb
    | true =>
      simp only [d131966, d181797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131967 q = 1) (hb : d181798 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d131967, d181798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131967, d181798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131968 q = 1) (hb : d181799 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d131968, d181799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131968, d181799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131969 q = 1) (hb : d181800 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d131969, d181800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131969, d181800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131970 q = 1) (hb : d181801 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d131970, d181801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131970, d181801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131971 q = 1) (hb : d181802 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d131971, d181802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131971, d181802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41116 (p : Pattern) (ha : d131977 p = 1) (hb : d181808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131972 q = 1) (hb : d181803 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d131972, d181803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41115 q ha hb
    | true =>
      simp only [d131972, d181803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131973 q = 1) (hb : d181804 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d131973, d181804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131973, d181804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131974 q = 1) (hb : d181805 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d131974, d181805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131974, d181805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131975 q = 1) (hb : d181806 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d131975, d181806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131975, d181806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131976 q = 1) (hb : d181807 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d131976, d181807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131976, d181807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131977 q = 1) (hb : d181808 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d131977, d181808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131977, d181808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41117 (p : Pattern) (ha : d132592 p = 1) (hb : d181010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d18592 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d180925 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d132588 q = 1) (hb : d181006 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132588, d181006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132588, d181006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d18556 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d132589 q = 1) (hb : d181007 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132589, d181007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132589, d181007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d132590 q = 1) (hb : d181008 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132590, d181008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132590, d181008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d132591 q = 1) (hb : d181009 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132591, d181009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132591, d181009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d132592 q = 1) (hb : d181010 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132592, d181010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132592, d181010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41118 (p : Pattern) (ha : d132598 p = 1) (hb : d181614 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132593 q = 1) (hb : d181011 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132593, d181011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132593, d181011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41117 q ha hb
  have h2 (q : Pattern) (ha : d132594 q = 1) (hb : d181610 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132594, d181610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132594, d181610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d132595 q = 1) (hb : d181611 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132595, d181611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132595, d181611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d132596 q = 1) (hb : d181612 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132596, d181612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132596, d181612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132597 q = 1) (hb : d181613 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132597, d181613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132597, d181613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132598 q = 1) (hb : d181614 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132598, d181614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132598, d181614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41119 (p : Pattern) (ha : d132608 p = 1) (hb : d181624 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d18656 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d180957 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d132604 q = 1) (hb : d181620 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132604, d181620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132604, d181620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d18685 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d132605 q = 1) (hb : d181621 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132605, d181621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132605, d181621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d132606 q = 1) (hb : d181622 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132606, d181622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132606, d181622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d132607 q = 1) (hb : d181623 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132607, d181623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132607, d181623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d132608 q = 1) (hb : d181624 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132608, d181624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132608, d181624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41120 (p : Pattern) (ha : d132614 p = 1) (hb : d181630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132609 q = 1) (hb : d181625 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132609, d181625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132609, d181625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41119 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d18696 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d132610 q = 1) (hb : d181626 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132610, d181626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132610, d181626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d132611 q = 1) (hb : d181627 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132611, d181627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132611, d181627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132612 q = 1) (hb : d181628 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132612, d181628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132612, d181628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132613 q = 1) (hb : d181629 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132613, d181629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132613, d181629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d132614 q = 1) (hb : d181630 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132614, d181630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132614, d181630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41121 (p : Pattern) (ha : d132620 p = 1) (hb : d181636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d18570 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d132599 q = 1) (hb : d181615 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132599, d181615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132599, d181615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41118 q ha hb
  have h3 (q : Pattern) (ha : d132600 q = 1) (hb : d181616 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132600, d181616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132600, d181616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132601 q = 1) (hb : d181617 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132601, d181617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132601, d181617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d132602 q = 1) (hb : d181618 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132602, d181618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132602, d181618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132603 q = 1) (hb : d181619 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132603, d181619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132603, d181619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d132615 q = 1) (hb : d181631 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132615, d181631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132615, d181631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41120 q ha hb
  have h8 (q : Pattern) (ha : d132616 q = 1) (hb : d181632 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132616, d181632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132616, d181632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d132617 q = 1) (hb : d181633 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132617, d181633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132617, d181633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d132618 q = 1) (hb : d181634 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132618, d181634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132618, d181634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d132619 q = 1) (hb : d181635 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132619, d181635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132619, d181635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d132620 q = 1) (hb : d181636 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d132620, d181636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d132620, d181636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro41122 (p : Pattern) (ha : d132625 p = 1) (hb : d181642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d18758 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d181637 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d132621 q = 1) (hb : d181638 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132621, d181638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132621, d181638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d18802 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d132622 q = 1) (hb : d181639 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132622, d181639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132622, d181639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d132623 q = 1) (hb : d181640 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132623, d181640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132623, d181640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d132624 q = 1) (hb : d181641 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132624, d181641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132624, d181641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d132625 q = 1) (hb : d181642 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132625, d181642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132625, d181642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41123 (p : Pattern) (ha : d132631 p = 1) (hb : d181648 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132626 q = 1) (hb : d181643 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132626, d181643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132626, d181643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41122 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d18818 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d132627 q = 1) (hb : d181644 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132627, d181644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132627, d181644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d132628 q = 1) (hb : d181645 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132628, d181645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132628, d181645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132629 q = 1) (hb : d181646 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132629, d181646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132629, d181646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132630 q = 1) (hb : d181647 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132630, d181647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132630, d181647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d132631 q = 1) (hb : d181648 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132631, d181648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132631, d181648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41124 (p : Pattern) (ha : d132637 p = 1) (hb : d181654 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132632 q = 1) (hb : d181649 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132632, d181649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132632, d181649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41123 q ha hb
  have h2 (q : Pattern) (ha : d132633 q = 1) (hb : d181650 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132633, d181650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132633, d181650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d132634 q = 1) (hb : d181651 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132634, d181651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132634, d181651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132635 q = 1) (hb : d181652 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132635, d181652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132635, d181652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d132636 q = 1) (hb : d181653 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132636, d181653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132636, d181653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132637 q = 1) (hb : d181654 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d132637, d181654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132637, d181654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41125 (p : Pattern) (ha : d132643 p = 1) (hb : d181661 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d18902 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d181656 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d132639 q = 1) (hb : d181657 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132639, d181657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132639, d181657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d18961 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d132640 q = 1) (hb : d181658 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132640, d181658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132640, d181658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d132641 q = 1) (hb : d181659 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132641, d181659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132641, d181659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d132642 q = 1) (hb : d181660 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132642, d181660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132642, d181660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d132643 q = 1) (hb : d181661 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132643, d181661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132643, d181661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41126 (p : Pattern) (ha : d132649 p = 1) (hb : d181667 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132644 q = 1) (hb : d181662 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132644, d181662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132644, d181662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41125 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d18977 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d132645 q = 1) (hb : d181663 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132645, d181663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132645, d181663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d132646 q = 1) (hb : d181664 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132646, d181664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132646, d181664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132647 q = 1) (hb : d181665 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132647, d181665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132647, d181665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132648 q = 1) (hb : d181666 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132648, d181666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132648, d181666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d132649 q = 1) (hb : d181667 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132649, d181667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132649, d181667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41127 (p : Pattern) (ha : d132655 p = 1) (hb : d181673 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132650 q = 1) (hb : d181668 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132650, d181668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132650, d181668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41126 q ha hb
  have h2 (q : Pattern) (ha : d132651 q = 1) (hb : d181669 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132651, d181669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132651, d181669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d132652 q = 1) (hb : d181670 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132652, d181670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132652, d181670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132653 q = 1) (hb : d181671 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132653, d181671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132653, d181671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d132654 q = 1) (hb : d181672 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132654, d181672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132654, d181672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132655 q = 1) (hb : d181673 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d132655, d181673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132655, d181673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41128 (p : Pattern) (ha : d132662 p = 1) (hb : d181689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d19099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d181684 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d132658 q = 1) (hb : d181685 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132658, d181685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132658, d181685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d19192 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d132659 q = 1) (hb : d181686 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132659, d181686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132659, d181686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d132660 q = 1) (hb : d181687 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132660, d181687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132660, d181687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d132661 q = 1) (hb : d181688 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132661, d181688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132661, d181688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d132662 q = 1) (hb : d181689 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132662, d181689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132662, d181689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41129 (p : Pattern) (ha : d132668 p = 1) (hb : d181695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132663 q = 1) (hb : d181690 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132663, d181690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132663, d181690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41128 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d19208 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d132664 q = 1) (hb : d181691 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132664, d181691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132664, d181691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d132665 q = 1) (hb : d181692 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132665, d181692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132665, d181692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132666 q = 1) (hb : d181693 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132666, d181693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132666, d181693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132667 q = 1) (hb : d181694 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132667, d181694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132667, d181694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d132668 q = 1) (hb : d181695 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132668, d181695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132668, d181695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41130 (p : Pattern) (ha : d132674 p = 1) (hb : d181701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132669 q = 1) (hb : d181696 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132669, d181696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132669, d181696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41129 q ha hb
  have h2 (q : Pattern) (ha : d132670 q = 1) (hb : d181697 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132670, d181697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132670, d181697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d132671 q = 1) (hb : d181698 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132671, d181698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132671, d181698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132672 q = 1) (hb : d181699 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132672, d181699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132672, d181699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d132673 q = 1) (hb : d181700 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132673, d181700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132673, d181700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132674 q = 1) (hb : d181701 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d132674, d181701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132674, d181701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41131 (p : Pattern) (ha : d132682 p = 1) (hb : d181718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d19334 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d181713 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d132678 q = 1) (hb : d181714 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132678, d181714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132678, d181714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d19430 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d132679 q = 1) (hb : d181715 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132679, d181715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132679, d181715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d132680 q = 1) (hb : d181716 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132680, d181716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132680, d181716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d132681 q = 1) (hb : d181717 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132681, d181717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132681, d181717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d132682 q = 1) (hb : d181718 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132682, d181718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132682, d181718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41132 (p : Pattern) (ha : d132688 p = 1) (hb : d181724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132683 q = 1) (hb : d181719 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132683, d181719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132683, d181719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41131 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d19446 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d132684 q = 1) (hb : d181720 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132684, d181720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132684, d181720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d132685 q = 1) (hb : d181721 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132685, d181721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132685, d181721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132686 q = 1) (hb : d181722 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132686, d181722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132686, d181722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132687 q = 1) (hb : d181723 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132687, d181723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132687, d181723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d132688 q = 1) (hb : d181724 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132688, d181724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132688, d181724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41133 (p : Pattern) (ha : d132694 p = 1) (hb : d181730 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132689 q = 1) (hb : d181725 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132689, d181725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132689, d181725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41132 q ha hb
  have h2 (q : Pattern) (ha : d132690 q = 1) (hb : d181726 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132690, d181726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132690, d181726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d132691 q = 1) (hb : d181727 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132691, d181727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132691, d181727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132692 q = 1) (hb : d181728 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132692, d181728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132692, d181728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d132693 q = 1) (hb : d181729 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132693, d181729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132693, d181729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132694 q = 1) (hb : d181730 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d132694, d181730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132694, d181730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41134 (p : Pattern) (ha : d132703 p = 1) (hb : d181748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d19566 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d181743 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d132699 q = 1) (hb : d181744 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132699, d181744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132699, d181744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d19662 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d132700 q = 1) (hb : d181745 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132700, d181745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132700, d181745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d132701 q = 1) (hb : d181746 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132701, d181746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132701, d181746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d132702 q = 1) (hb : d181747 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132702, d181747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132702, d181747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d132703 q = 1) (hb : d181748 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132703, d181748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132703, d181748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41135 (p : Pattern) (ha : d132709 p = 1) (hb : d181754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132704 q = 1) (hb : d181749 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132704, d181749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132704, d181749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41134 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d19678 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d132705 q = 1) (hb : d181750 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132705, d181750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132705, d181750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d132706 q = 1) (hb : d181751 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132706, d181751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132706, d181751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132707 q = 1) (hb : d181752 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132707, d181752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132707, d181752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132708 q = 1) (hb : d181753 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132708, d181753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132708, d181753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d132709 q = 1) (hb : d181754 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132709, d181754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132709, d181754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41136 (p : Pattern) (ha : d132715 p = 1) (hb : d181760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132710 q = 1) (hb : d181755 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132710, d181755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132710, d181755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41135 q ha hb
  have h2 (q : Pattern) (ha : d132711 q = 1) (hb : d181756 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132711, d181756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132711, d181756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d132712 q = 1) (hb : d181757 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132712, d181757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132712, d181757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132713 q = 1) (hb : d181758 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132713, d181758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132713, d181758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d132714 q = 1) (hb : d181759 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132714, d181759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132714, d181759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132715 q = 1) (hb : d181760 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d132715, d181760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132715, d181760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41137 (p : Pattern) (ha : d132721 p = 1) (hb : d181766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d132638 q = 1) (hb : d181655 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d132638, d181655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41121 q ha hb
    | true =>
      simp only [d132638, d181655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41124 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d132656 q = 1) (hb : d181674 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d132656, d181674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132656, d181674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41127 q ha hb
  have h3 (q : Pattern) (ha : d132657 q = 1) (hb : d181675 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d132657, d181675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132657, d181675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d132675 q = 1) (hb : d181702 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d132675, d181702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132675, d181702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41130 q ha hb
  have h5 (q : Pattern) (ha : d132676 q = 1) (hb : d181703 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d132676, d181703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132676, d181703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d132677 q = 1) (hb : d181704 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d132677, d181704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132677, d181704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d132695 q = 1) (hb : d181731 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d132695, d181731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132695, d181731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41133 q ha hb
  have h8 (q : Pattern) (ha : d132696 q = 1) (hb : d181732 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d132696, d181732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132696, d181732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d132697 q = 1) (hb : d181733 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d132697, d181733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132697, d181733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d132698 q = 1) (hb : d181734 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d132698, d181734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d132698, d181734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d132716 q = 1) (hb : d181761 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d132716, d181761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132716, d181761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41136 q ha hb
  have h12 (q : Pattern) (ha : d132717 q = 1) (hb : d181762 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d132717, d181762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132717, d181762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d132718 q = 1) (hb : d181763 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d132718, d181763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132718, d181763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d132719 q = 1) (hb : d181764 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d132719, d181764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132719, d181764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d132720 q = 1) (hb : d181765 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d132720, d181765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d132720, d181765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d132721 q = 1) (hb : d181766 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d132721, d181766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d132721, d181766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro41138 (p : Pattern) (ha : d132727 p = 1) (hb : d181772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132722 q = 1) (hb : d181767 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d132722, d181767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41137 q ha hb
    | true =>
      simp only [d132722, d181767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d132723 q = 1) (hb : d181768 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d132723, d181768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132723, d181768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d132724 q = 1) (hb : d181769 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d132724, d181769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132724, d181769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d132725 q = 1) (hb : d181770 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d132725, d181770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132725, d181770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132726 q = 1) (hb : d181771 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d132726, d181771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132726, d181771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132727 q = 1) (hb : d181772 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d132727, d181772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132727, d181772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41139 (p : Pattern) (ha : d132733 p = 1) (hb : d181778 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132728 q = 1) (hb : d181773 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d132728, d181773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41138 q ha hb
    | true =>
      simp only [d132728, d181773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d132729 q = 1) (hb : d181774 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d132729, d181774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132729, d181774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d132730 q = 1) (hb : d181775 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d132730, d181775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132730, d181775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d132731 q = 1) (hb : d181776 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d132731, d181776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132731, d181776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132732 q = 1) (hb : d181777 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d132732, d181777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132732, d181777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132733 q = 1) (hb : d181778 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d132733, d181778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132733, d181778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41140 (p : Pattern) (ha : d132739 p = 1) (hb : d181784 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132734 q = 1) (hb : d181779 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d132734, d181779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41139 q ha hb
    | true =>
      simp only [d132734, d181779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d132735 q = 1) (hb : d181780 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d132735, d181780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132735, d181780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d132736 q = 1) (hb : d181781 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d132736, d181781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132736, d181781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d132737 q = 1) (hb : d181782 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d132737, d181782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132737, d181782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132738 q = 1) (hb : d181783 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d132738, d181783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132738, d181783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132739 q = 1) (hb : d181784 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d132739, d181784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132739, d181784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41141 (p : Pattern) (ha : d132745 p = 1) (hb : d181790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132740 q = 1) (hb : d181785 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d132740, d181785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41140 q ha hb
    | true =>
      simp only [d132740, d181785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d132741 q = 1) (hb : d181786 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d132741, d181786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132741, d181786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d132742 q = 1) (hb : d181787 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d132742, d181787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132742, d181787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d132743 q = 1) (hb : d181788 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d132743, d181788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132743, d181788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132744 q = 1) (hb : d181789 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d132744, d181789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132744, d181789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132745 q = 1) (hb : d181790 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d132745, d181790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132745, d181790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41142 (p : Pattern) (ha : d132751 p = 1) (hb : d181796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132746 q = 1) (hb : d181791 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d132746, d181791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41141 q ha hb
    | true =>
      simp only [d132746, d181791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d132747 q = 1) (hb : d181792 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d132747, d181792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132747, d181792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d132748 q = 1) (hb : d181793 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d132748, d181793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132748, d181793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d132749 q = 1) (hb : d181794 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d132749, d181794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132749, d181794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132750 q = 1) (hb : d181795 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d132750, d181795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132750, d181795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132751 q = 1) (hb : d181796 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d132751, d181796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132751, d181796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41143 (p : Pattern) (ha : d132757 p = 1) (hb : d181802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132752 q = 1) (hb : d181797 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d132752, d181797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41142 q ha hb
    | true =>
      simp only [d132752, d181797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d132753 q = 1) (hb : d181798 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d132753, d181798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132753, d181798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d132754 q = 1) (hb : d181799 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d132754, d181799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132754, d181799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d132755 q = 1) (hb : d181800 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d132755, d181800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132755, d181800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132756 q = 1) (hb : d181801 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d132756, d181801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132756, d181801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132757 q = 1) (hb : d181802 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d132757, d181802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132757, d181802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41144 (p : Pattern) (ha : d132763 p = 1) (hb : d181808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d132758 q = 1) (hb : d181803 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d132758, d181803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41143 q ha hb
    | true =>
      simp only [d132758, d181803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d132759 q = 1) (hb : d181804 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d132759, d181804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132759, d181804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d132760 q = 1) (hb : d181805 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d132760, d181805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132760, d181805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d132761 q = 1) (hb : d181806 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d132761, d181806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132761, d181806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d132762 q = 1) (hb : d181807 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d132762, d181807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132762, d181807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d132763 q = 1) (hb : d181808 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d132763, d181808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132763, d181808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41145 (p : Pattern) (ha : d17564 p = 1) (hb : d181811 p = 1) : d183573 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25 q = 1) (hb : d102052 q = 1) : d25 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d67 q = 1) (hb : d181810 q = 1) : d9292 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d181810, d9292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d67, d181810, d9292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17561 q = 1) (hb : d181811 q = 1) : d183570 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17561, d181811, d183570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17561, d181811, d183570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17562 q = 1) (hb : d181811 q = 1) : d183571 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17562, d183571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17562, d183571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17563 q = 1) (hb : d181811 q = 1) : d183572 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17563, d183572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17563, d183572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d17564 q = 1) (hb : d181811 q = 1) : d183573 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17564, d183573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17564, d183573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro41146 (p : Pattern) (ha : d17570 p = 1) (hb : d181811 p = 1) : d183579 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17565 q = 1) (hb : d181811 q = 1) : d183574 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17565, d183574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41145 q ha hb
    | true =>
      simp only [d17565, d183574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17566 q = 1) (hb : d181811 q = 1) : d183575 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17566, d183575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17566, d183575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17567 q = 1) (hb : d181811 q = 1) : d183576 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17567, d183576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17567, d183576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17568 q = 1) (hb : d181811 q = 1) : d183577 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17568, d183577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17568, d183577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17569 q = 1) (hb : d181811 q = 1) : d183578 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17569, d183578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17569, d183578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17570 q = 1) (hb : d181811 q = 1) : d183579 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17570, d183579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17570, d183579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41147 (p : Pattern) (ha : d17576 p = 1) (hb : d181811 p = 1) : d183585 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17571 q = 1) (hb : d181811 q = 1) : d183580 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17571, d183580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41146 q ha hb
    | true =>
      simp only [d17571, d183580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17572 q = 1) (hb : d181811 q = 1) : d183581 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17572, d183581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17572, d183581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17573 q = 1) (hb : d181811 q = 1) : d183582 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17573, d183582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17573, d183582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17574 q = 1) (hb : d181811 q = 1) : d183583 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17574, d183583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17574, d183583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17575 q = 1) (hb : d181811 q = 1) : d183584 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17575, d183584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17575, d183584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17576 q = 1) (hb : d181811 q = 1) : d183585 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17576, d183585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17576, d183585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41148 (p : Pattern) (ha : d17582 p = 1) (hb : d181811 p = 1) : d183591 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17577 q = 1) (hb : d181811 q = 1) : d183586 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17577, d183586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41147 q ha hb
    | true =>
      simp only [d17577, d183586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17578 q = 1) (hb : d181811 q = 1) : d183587 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17578, d183587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17578, d183587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17579 q = 1) (hb : d181811 q = 1) : d183588 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17579, d183588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17579, d183588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17580 q = 1) (hb : d181811 q = 1) : d183589 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17580, d183589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17580, d183589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17581 q = 1) (hb : d181811 q = 1) : d183590 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17581, d183590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17581, d183590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17582 q = 1) (hb : d181811 q = 1) : d183591 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17582, d183591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17582, d183591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41149 (p : Pattern) (ha : d17588 p = 1) (hb : d181811 p = 1) : d183597 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17583 q = 1) (hb : d181811 q = 1) : d183592 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17583, d183592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17583, d183592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41148 q ha hb
  have h2 (q : Pattern) (ha : d17584 q = 1) (hb : d181811 q = 1) : d183593 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d17584, d183593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17584, d183593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17585 q = 1) (hb : d181811 q = 1) : d183594 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d17585, d183594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17585, d183594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17586 q = 1) (hb : d181811 q = 1) : d183595 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d17586, d183595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17586, d183595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17587 q = 1) (hb : d181811 q = 1) : d183596 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d17587, d183596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17587, d183596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17588 q = 1) (hb : d181811 q = 1) : d183597 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d17588, d183597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17588, d183597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41150 (p : Pattern) (ha : d17596 p = 1) (hb : d181811 p = 1) : d183605 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d226 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d139 q = 1) (hb : d102052 q = 1) : d139 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d227 q = 1) (hb : d181810 q = 1) : d9325 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d181810, d9325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d227, d181810, d9325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17593 q = 1) (hb : d181811 q = 1) : d183602 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17593, d181811, d183602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17593, d181811, d183602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17594 q = 1) (hb : d181811 q = 1) : d183603 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17594, d183603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17594, d183603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d66 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d25 q = 1) (hb : d102052 q = 1) : d25 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d67 q = 1) (hb : d181810 q = 1) : d9292 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d181810, d9292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d67, d181810, d9292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17561 q = 1) (hb : d181811 q = 1) : d183570 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17561, d181811, d183570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17561, d181811, d183570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d17562 q = 1) (hb : d181811 q = 1) : d183571 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17562, d183571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17562, d183571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d17595 q = 1) (hb : d181811 q = 1) : d183604 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17595, d183604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17595, d183604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17563 q = 1) (hb : d181811 q = 1) : d183572 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17563, d183572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17563, d183572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d17596 q = 1) (hb : d181811 q = 1) : d183605 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17596, d183605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17596, d183605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro41151 (p : Pattern) (ha : d17602 p = 1) (hb : d181811 p = 1) : d183611 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17597 q = 1) (hb : d181811 q = 1) : d183606 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17597, d183606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41150 q ha hb
    | true =>
      simp only [d17597, d183606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41145 q ha hb
  have h2 (q : Pattern) (ha : d17598 q = 1) (hb : d181811 q = 1) : d183607 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17598, d183607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17598, d183607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17599 q = 1) (hb : d181811 q = 1) : d183608 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17599, d183608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17599, d183608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17565 q = 1) (hb : d181811 q = 1) : d183574 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17565, d183574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41145 q ha hb
    | true =>
      simp only [d17565, d183574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17566 q = 1) (hb : d181811 q = 1) : d183575 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17566, d183575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17566, d183575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17567 q = 1) (hb : d181811 q = 1) : d183576 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17567, d183576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17567, d183576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17600 q = 1) (hb : d181811 q = 1) : d183609 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17600, d183609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17600, d183609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17568 q = 1) (hb : d181811 q = 1) : d183577 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17568, d183577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17568, d183577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17601 q = 1) (hb : d181811 q = 1) : d183610 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17601, d183610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17601, d183610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17602 q = 1) (hb : d181811 q = 1) : d183611 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17602, d183611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17602, d183611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro41152 (p : Pattern) (ha : d17608 p = 1) (hb : d181811 p = 1) : d183617 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17603 q = 1) (hb : d181811 q = 1) : d183612 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17603, d183612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41151 q ha hb
    | true =>
      simp only [d17603, d183612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17604 q = 1) (hb : d181811 q = 1) : d183613 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17604, d183613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17604, d183613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17571 q = 1) (hb : d181811 q = 1) : d183580 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17571, d183580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41146 q ha hb
    | true =>
      simp only [d17571, d183580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17572 q = 1) (hb : d181811 q = 1) : d183581 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17572, d183581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17572, d183581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17605 q = 1) (hb : d181811 q = 1) : d183614 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17605, d183614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17605, d183614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17606 q = 1) (hb : d181811 q = 1) : d183615 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17606, d183615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17606, d183615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17607 q = 1) (hb : d181811 q = 1) : d183616 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17607, d183616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17607, d183616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17608 q = 1) (hb : d181811 q = 1) : d183617 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17608, d183617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17608, d183617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41153 (p : Pattern) (ha : d60563 p = 1) (hb : d181811 p = 1) : d183623 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17609 q = 1) (hb : d181811 q = 1) : d183618 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17609, d183618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41152 q ha hb
    | true =>
      simp only [d17609, d183618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41147 q ha hb
  have h2 (q : Pattern) (ha : d60559 q = 1) (hb : d181811 q = 1) : d183619 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d60559, d183619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60559, d183619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17577 q = 1) (hb : d181811 q = 1) : d183586 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17577, d183586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41147 q ha hb
    | true =>
      simp only [d17577, d183586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17578 q = 1) (hb : d181811 q = 1) : d183587 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17578, d183587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17578, d183587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d60560 q = 1) (hb : d181811 q = 1) : d183620 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d60560, d183620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d60560, d183620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60561 q = 1) (hb : d181811 q = 1) : d183621 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d60561, d183621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60561, d183621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d60562 q = 1) (hb : d181811 q = 1) : d183622 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d60562, d183622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60562, d183622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d60563 q = 1) (hb : d181811 q = 1) : d183623 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d60563, d183623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60563, d183623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41154 (p : Pattern) (ha : d60569 p = 1) (hb : d181811 p = 1) : d183629 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d60564 q = 1) (hb : d181811 q = 1) : d183624 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d60564, d183624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60564, d183624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41153 q ha hb
  have h2 (q : Pattern) (ha : d60565 q = 1) (hb : d181811 q = 1) : d183625 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d60565, d183625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60565, d183625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d60566 q = 1) (hb : d181811 q = 1) : d183626 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d60566, d183626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d60566, d183626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d60567 q = 1) (hb : d181811 q = 1) : d183627 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d60567, d183627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d60567, d183627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d60568 q = 1) (hb : d181811 q = 1) : d183628 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d60568, d183628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d60568, d183628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d60569 q = 1) (hb : d181811 q = 1) : d183629 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d60569, d183629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60569, d183629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41155 (p : Pattern) (ha : d17696 p = 1) (hb : d181811 p = 1) : d183671 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17577 q = 1) (hb : d181811 q = 1) : d183586 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17577, d183586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41147 q ha hb
    | true =>
      simp only [d17577, d183586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17692 q = 1) (hb : d181811 q = 1) : d183667 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17692, d183667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17692, d183667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17693 q = 1) (hb : d181811 q = 1) : d183668 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17693, d183668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17693, d183668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17694 q = 1) (hb : d181811 q = 1) : d183669 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17694, d183669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17694, d183669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17695 q = 1) (hb : d181811 q = 1) : d183670 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17695, d183670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17695, d183670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17696 q = 1) (hb : d181811 q = 1) : d183671 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17696, d183671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17696, d183671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41156 (p : Pattern) (ha : d17649 p = 1) (hb : d181811 p = 1) : d183641 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d412 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d102052 q = 1) : d319 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d413 q = 1) (hb : d181810 q = 1) : d9377 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d181810, d9377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d413, d181810, d9377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17643 q = 1) (hb : d181811 q = 1) : d183635 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17643, d181811, d183635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17643, d181811, d183635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17644 q = 1) (hb : d181811 q = 1) : d183636 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17644, d183636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17644, d183636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d226 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d139 q = 1) (hb : d102052 q = 1) : d139 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d227 q = 1) (hb : d181810 q = 1) : d9325 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d181810, d9325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d227, d181810, d9325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17593 q = 1) (hb : d181811 q = 1) : d183602 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17593, d181811, d183602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17593, d181811, d183602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d17594 q = 1) (hb : d181811 q = 1) : d183603 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17594, d183603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17594, d183603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d17645 q = 1) (hb : d181811 q = 1) : d183637 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17645, d183637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17645, d183637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d12599 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d9382 q = 1) (hb : d102052 q = 1) : d9382 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d12600 q = 1) (hb : d181810 q = 1) : d9383 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d181810, d9383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d12600, d181810, d9383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17646 q = 1) (hb : d181811 q = 1) : d183638 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17646, d181811, d183638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d17646, d181811, d183638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h17 (q : Pattern) (ha : d17647 q = 1) (hb : d181811 q = 1) : d183639 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17647, d183639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17647, d183639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d66 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d25 q = 1) (hb : d102052 q = 1) : d25 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d67 q = 1) (hb : d181810 q = 1) : d9292 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d181810, d9292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d67, d181810, d9292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d17561 q = 1) (hb : d181811 q = 1) : d183570 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17561, d181811, d183570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d17561, d181811, d183570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h22 (q : Pattern) (ha : d17562 q = 1) (hb : d181811 q = 1) : d183571 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17562, d183571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d17562, d183571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h23 (q : Pattern) (ha : d17648 q = 1) (hb : d181811 q = 1) : d183640 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17648, d183640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d17648, d183640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d17649 q = 1) (hb : d181811 q = 1) : d183641 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17649, d183641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17649, d183641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro41157 (p : Pattern) (ha : d17655 p = 1) (hb : d181811 p = 1) : d183647 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17650 q = 1) (hb : d181811 q = 1) : d183642 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17650, d183642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41156 q ha hb
    | true =>
      simp only [d17650, d183642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41150 q ha hb
  have h2 (q : Pattern) (ha : d17651 q = 1) (hb : d181811 q = 1) : d183643 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17651, d183643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17651, d183643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17652 q = 1) (hb : d181811 q = 1) : d183644 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17652, d183644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17652, d183644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17597 q = 1) (hb : d181811 q = 1) : d183606 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17597, d183606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41150 q ha hb
    | true =>
      simp only [d17597, d183606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41145 q ha hb
  have h5 (q : Pattern) (ha : d17598 q = 1) (hb : d181811 q = 1) : d183607 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17598, d183607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17598, d183607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17599 q = 1) (hb : d181811 q = 1) : d183608 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17599, d183608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17599, d183608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17653 q = 1) (hb : d181811 q = 1) : d183645 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17653, d183645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17653, d183645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17565 q = 1) (hb : d181811 q = 1) : d183574 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17565, d183574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41145 q ha hb
    | true =>
      simp only [d17565, d183574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17566 q = 1) (hb : d181811 q = 1) : d183575 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17566, d183575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17566, d183575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17567 q = 1) (hb : d181811 q = 1) : d183576 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17567, d183576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17567, d183576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17600 q = 1) (hb : d181811 q = 1) : d183609 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17600, d183609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17600, d183609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17654 q = 1) (hb : d181811 q = 1) : d183646 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17654, d183646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17654, d183646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17655 q = 1) (hb : d181811 q = 1) : d183647 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17655, d183647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17655, d183647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro41158 (p : Pattern) (ha : d17661 p = 1) (hb : d181811 p = 1) : d183653 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17656 q = 1) (hb : d181811 q = 1) : d183648 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17656, d183648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41157 q ha hb
    | true =>
      simp only [d17656, d183648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17657 q = 1) (hb : d181811 q = 1) : d183649 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17657, d183649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17657, d183649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17603 q = 1) (hb : d181811 q = 1) : d183612 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17603, d183612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41151 q ha hb
    | true =>
      simp only [d17603, d183612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17604 q = 1) (hb : d181811 q = 1) : d183613 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17604, d183613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17604, d183613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17658 q = 1) (hb : d181811 q = 1) : d183650 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17658, d183650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17658, d183650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17659 q = 1) (hb : d181811 q = 1) : d183651 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17659, d183651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17659, d183651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17660 q = 1) (hb : d181811 q = 1) : d183652 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17660, d183652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17660, d183652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17661 q = 1) (hb : d181811 q = 1) : d183653 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17661, d183653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17661, d183653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41159 (p : Pattern) (ha : d17684 p = 1) (hb : d181811 p = 1) : d183659 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17603 q = 1) (hb : d181811 q = 1) : d183612 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17603, d183612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41151 q ha hb
    | true =>
      simp only [d17603, d183612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17604 q = 1) (hb : d181811 q = 1) : d183613 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17604, d183613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17604, d183613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17681 q = 1) (hb : d181811 q = 1) : d183656 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17681, d183656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17681, d183656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17682 q = 1) (hb : d181811 q = 1) : d183657 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17682, d183657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17682, d183657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17683 q = 1) (hb : d181811 q = 1) : d183658 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17683, d183658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17683, d183658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17684 q = 1) (hb : d181811 q = 1) : d183659 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17684, d183659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17684, d183659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41160 (p : Pattern) (ha : d129315 p = 1) (hb : d181811 p = 1) : d183665 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17662 q = 1) (hb : d181811 q = 1) : d183654 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17662, d183654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41158 q ha hb
    | true =>
      simp only [d17662, d183654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41152 q ha hb
  have h2 (q : Pattern) (ha : d129311 q = 1) (hb : d181811 q = 1) : d183655 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129311, d183655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129311, d183655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17685 q = 1) (hb : d181811 q = 1) : d183660 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17685, d183660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41159 q ha hb
    | true =>
      simp only [d17685, d183660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17686 q = 1) (hb : d181811 q = 1) : d183661 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17686, d183661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17686, d183661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129312 q = 1) (hb : d181811 q = 1) : d183662 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129312, d183662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129312, d183662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129313 q = 1) (hb : d181811 q = 1) : d183663 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129313, d183663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129313, d183663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129314 q = 1) (hb : d181811 q = 1) : d183664 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129314, d183664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129314, d183664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129315 q = 1) (hb : d181811 q = 1) : d183665 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129315, d183665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129315, d183665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41161 (p : Pattern) (ha : d129321 p = 1) (hb : d181811 p = 1) : d183677 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129316 q = 1) (hb : d181811 q = 1) : d183666 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129316, d183666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129316, d183666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41160 q ha hb
  have h2 (q : Pattern) (ha : d17697 q = 1) (hb : d181811 q = 1) : d183672 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17697, d183672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17697, d183672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41155 q ha hb
  have h3 (q : Pattern) (ha : d129317 q = 1) (hb : d181811 q = 1) : d183673 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129317, d183673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129317, d183673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129318 q = 1) (hb : d181811 q = 1) : d183674 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129318, d183674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129318, d183674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129319 q = 1) (hb : d181811 q = 1) : d183675 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129319, d183675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129319, d183675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129320 q = 1) (hb : d181811 q = 1) : d183676 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129320, d183676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129320, d183676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129321 q = 1) (hb : d181811 q = 1) : d183677 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129321, d183677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129321, d183677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41162 (p : Pattern) (ha : d129327 p = 1) (hb : d181811 p = 1) : d183683 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17589 q = 1) (hb : d181811 q = 1) : d183598 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d17589, d183598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17589, d183598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41149 q ha hb
  have h2 (q : Pattern) (ha : d17590 q = 1) (hb : d181811 q = 1) : d183599 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d17590, d183599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17590, d183599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17591 q = 1) (hb : d181811 q = 1) : d183600 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d17591, d183600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17591, d183600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17592 q = 1) (hb : d181811 q = 1) : d183601 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d17592, d183601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17592, d183601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d60570 q = 1) (hb : d181811 q = 1) : d183630 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60570, d183630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60570, d183630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41154 q ha hb
  have h6 (q : Pattern) (ha : d60571 q = 1) (hb : d181811 q = 1) : d183631 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60571, d183631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60571, d183631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d60572 q = 1) (hb : d181811 q = 1) : d183632 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60572, d183632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60572, d183632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d60573 q = 1) (hb : d181811 q = 1) : d183633 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60573, d183633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60573, d183633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d60574 q = 1) (hb : d181811 q = 1) : d183634 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d60574, d183634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d60574, d183634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129322 q = 1) (hb : d181811 q = 1) : d183678 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129322, d183678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129322, d183678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41161 q ha hb
  have h11 (q : Pattern) (ha : d129323 q = 1) (hb : d181811 q = 1) : d183679 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129323, d183679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129323, d183679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d129324 q = 1) (hb : d181811 q = 1) : d183680 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129324, d183680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129324, d183680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d129325 q = 1) (hb : d181811 q = 1) : d183681 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129325, d183681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129325, d183681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d129326 q = 1) (hb : d181811 q = 1) : d183682 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129326, d183682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129326, d183682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d129327 q = 1) (hb : d181811 q = 1) : d183683 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129327, d183683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d129327, d183683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro41163 (p : Pattern) (ha : d17740 p = 1) (hb : d181811 p = 1) : d183715 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17597 q = 1) (hb : d181811 q = 1) : d183606 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17597, d183606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41150 q ha hb
    | true =>
      simp only [d17597, d183606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41145 q ha hb
  have h2 (q : Pattern) (ha : d17598 q = 1) (hb : d181811 q = 1) : d183607 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17598, d183607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17598, d183607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17599 q = 1) (hb : d181811 q = 1) : d183608 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17599, d183608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17599, d183608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17730 q = 1) (hb : d181811 q = 1) : d183705 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17730, d183705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17730, d183705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17739 q = 1) (hb : d181811 q = 1) : d183714 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17739, d183714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17739, d183714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17740 q = 1) (hb : d181811 q = 1) : d183715 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17740, d183715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17740, d183715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41164 (p : Pattern) (ha : d17792 p = 1) (hb : d181811 p = 1) : d183738 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17741 q = 1) (hb : d181811 q = 1) : d183716 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17741, d183716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41163 q ha hb
    | true =>
      simp only [d17741, d183716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17742 q = 1) (hb : d181811 q = 1) : d183717 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17742, d183717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17742, d183717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17789 q = 1) (hb : d181811 q = 1) : d183735 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17789, d183735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17789, d183735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17790 q = 1) (hb : d181811 q = 1) : d183736 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17790, d183736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17790, d183736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17791 q = 1) (hb : d181811 q = 1) : d183737 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17791, d183737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17791, d183737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17792 q = 1) (hb : d181811 q = 1) : d183738 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17792, d183738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17792, d183738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41165 (p : Pattern) (ha : d17798 p = 1) (hb : d181811 p = 1) : d183744 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17793 q = 1) (hb : d181811 q = 1) : d183739 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17793, d183739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41164 q ha hb
    | true =>
      simp only [d17793, d183739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17794 q = 1) (hb : d181811 q = 1) : d183740 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17794, d183740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17794, d183740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17795 q = 1) (hb : d181811 q = 1) : d183741 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17795, d183741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17795, d183741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17796 q = 1) (hb : d181811 q = 1) : d183742 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17796, d183742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17796, d183742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17797 q = 1) (hb : d181811 q = 1) : d183743 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17797, d183743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17797, d183743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17798 q = 1) (hb : d181811 q = 1) : d183744 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17798, d183744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17798, d183744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41166 (p : Pattern) (ha : d17717 p = 1) (hb : d181811 p = 1) : d183692 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d659 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d543 q = 1) (hb : d102052 q = 1) : d543 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d660 q = 1) (hb : d181810 q = 1) : d9449 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, d181810, d9449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d660, d181810, d9449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17709 q = 1) (hb : d181811 q = 1) : d183684 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17709, d181811, d183684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17709, d181811, d183684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17710 q = 1) (hb : d181811 q = 1) : d183685 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17710, d183685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17710, d183685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d16156 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9458 q = 1) (hb : d102052 q = 1) : d9458 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d16157 q = 1) (hb : d181810 q = 1) : d9459 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16157, d181810, d9459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d16157, d181810, d9459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17711 q = 1) (hb : d181811 q = 1) : d183686 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17711, d181811, d183686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17711, d181811, d183686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d17712 q = 1) (hb : d181811 q = 1) : d183687 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17712, d183687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17712, d183687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d17713 q = 1) (hb : d181811 q = 1) : d183688 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17713, d183688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17713, d183688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d12858 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d9468 q = 1) (hb : d102052 q = 1) : d9468 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d12859 q = 1) (hb : d181810 q = 1) : d9469 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d181810, d9469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d12859, d181810, d9469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17714 q = 1) (hb : d181811 q = 1) : d183689 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17714, d181811, d183689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d17714, d181811, d183689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h17 (q : Pattern) (ha : d17715 q = 1) (hb : d181811 q = 1) : d183690 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17715, d183690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17715, d183690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d12599 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d9382 q = 1) (hb : d102052 q = 1) : d9382 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d12600 q = 1) (hb : d181810 q = 1) : d9383 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d181810, d9383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d12600, d181810, d9383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d17646 q = 1) (hb : d181811 q = 1) : d183638 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17646, d181811, d183638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d17646, d181811, d183638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h22 (q : Pattern) (ha : d17647 q = 1) (hb : d181811 q = 1) : d183639 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17647, d183639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d17647, d183639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h23 (q : Pattern) (ha : d17716 q = 1) (hb : d181811 q = 1) : d183691 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17716, d183691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d17716, d183691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d17717 q = 1) (hb : d181811 q = 1) : d183692 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17717, d183692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17717, d183692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro41167 (p : Pattern) (ha : d17721 p = 1) (hb : d181811 p = 1) : d183696 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12599 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9382 q = 1) (hb : d102052 q = 1) : d9382 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12600 q = 1) (hb : d181810 q = 1) : d9383 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d181810, d9383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12600, d181810, d9383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17646 q = 1) (hb : d181811 q = 1) : d183638 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17646, d181811, d183638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17646, d181811, d183638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17647 q = 1) (hb : d181811 q = 1) : d183639 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17647, d183639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17647, d183639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d66 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d25 q = 1) (hb : d102052 q = 1) : d25 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d67 q = 1) (hb : d181810 q = 1) : d9292 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d181810, d9292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d67, d181810, d9292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17561 q = 1) (hb : d181811 q = 1) : d183570 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17561, d181811, d183570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17561, d181811, d183570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d17562 q = 1) (hb : d181811 q = 1) : d183571 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17562, d183571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17562, d183571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d17648 q = 1) (hb : d181811 q = 1) : d183640 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17648, d183640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17648, d183640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17563 q = 1) (hb : d181811 q = 1) : d183572 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17563, d183572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17563, d183572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d17721 q = 1) (hb : d181811 q = 1) : d183696 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17721, d183696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17721, d183696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro41168 (p : Pattern) (ha : d17727 p = 1) (hb : d181811 p = 1) : d183702 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17718 q = 1) (hb : d181811 q = 1) : d183693 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17718, d183693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41166 q ha hb
    | true =>
      simp only [d17718, d183693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41156 q ha hb
  have h2 (q : Pattern) (ha : d17719 q = 1) (hb : d181811 q = 1) : d183694 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17719, d183694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17719, d183694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17720 q = 1) (hb : d181811 q = 1) : d183695 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17720, d183695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17720, d183695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17722 q = 1) (hb : d181811 q = 1) : d183697 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17722, d183697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41156 q ha hb
    | true =>
      simp only [d17722, d183697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41167 q ha hb
  have h5 (q : Pattern) (ha : d17723 q = 1) (hb : d181811 q = 1) : d183698 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17723, d183698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17723, d183698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17724 q = 1) (hb : d181811 q = 1) : d183699 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17724, d183699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17724, d183699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17725 q = 1) (hb : d181811 q = 1) : d183700 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17725, d183700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17725, d183700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17650 q = 1) (hb : d181811 q = 1) : d183642 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17650, d183642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41156 q ha hb
    | true =>
      simp only [d17650, d183642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41150 q ha hb
  have h9 (q : Pattern) (ha : d17651 q = 1) (hb : d181811 q = 1) : d183643 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17651, d183643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17651, d183643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17652 q = 1) (hb : d181811 q = 1) : d183644 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17652, d183644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17652, d183644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17597 q = 1) (hb : d181811 q = 1) : d183606 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17597, d183606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41150 q ha hb
    | true =>
      simp only [d17597, d183606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41145 q ha hb
  have h12 (q : Pattern) (ha : d17598 q = 1) (hb : d181811 q = 1) : d183607 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17598, d183607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17598, d183607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17599 q = 1) (hb : d181811 q = 1) : d183608 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17599, d183608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17599, d183608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17653 q = 1) (hb : d181811 q = 1) : d183645 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17653, d183645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17653, d183645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17726 q = 1) (hb : d181811 q = 1) : d183701 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17726, d183701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17726, d183701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17727 q = 1) (hb : d181811 q = 1) : d183702 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17727, d183702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d17727, d183702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro41169 (p : Pattern) (ha : d17732 p = 1) (hb : d181811 p = 1) : d183707 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17650 q = 1) (hb : d181811 q = 1) : d183642 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17650, d183642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41156 q ha hb
    | true =>
      simp only [d17650, d183642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41150 q ha hb
  have h2 (q : Pattern) (ha : d17651 q = 1) (hb : d181811 q = 1) : d183643 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17651, d183643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17651, d183643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17652 q = 1) (hb : d181811 q = 1) : d183644 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17652, d183644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17652, d183644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17597 q = 1) (hb : d181811 q = 1) : d183606 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17597, d183606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41150 q ha hb
    | true =>
      simp only [d17597, d183606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41145 q ha hb
  have h5 (q : Pattern) (ha : d17598 q = 1) (hb : d181811 q = 1) : d183607 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17598, d183607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17598, d183607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17599 q = 1) (hb : d181811 q = 1) : d183608 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17599, d183608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17599, d183608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17653 q = 1) (hb : d181811 q = 1) : d183645 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17653, d183645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17653, d183645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17730 q = 1) (hb : d181811 q = 1) : d183705 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17730, d183705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17730, d183705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17731 q = 1) (hb : d181811 q = 1) : d183706 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17731, d183706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17731, d183706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17732 q = 1) (hb : d181811 q = 1) : d183707 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17732, d183707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17732, d183707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro41170 (p : Pattern) (ha : d17738 p = 1) (hb : d181811 p = 1) : d183713 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17728 q = 1) (hb : d181811 q = 1) : d183703 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17728, d183703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41168 q ha hb
    | true =>
      simp only [d17728, d183703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17729 q = 1) (hb : d181811 q = 1) : d183704 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17729, d183704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17729, d183704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17733 q = 1) (hb : d181811 q = 1) : d183708 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17733, d183708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41169 q ha hb
    | true =>
      simp only [d17733, d183708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17734 q = 1) (hb : d181811 q = 1) : d183709 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17734, d183709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17734, d183709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17735 q = 1) (hb : d181811 q = 1) : d183710 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17735, d183710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17735, d183710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17736 q = 1) (hb : d181811 q = 1) : d183711 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17736, d183711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17736, d183711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17737 q = 1) (hb : d181811 q = 1) : d183712 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17737, d183712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17737, d183712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17738 q = 1) (hb : d181811 q = 1) : d183713 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17738, d183713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17738, d183713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41171 (p : Pattern) (ha : d17746 p = 1) (hb : d181811 p = 1) : d183721 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17733 q = 1) (hb : d181811 q = 1) : d183708 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17733, d183708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41169 q ha hb
    | true =>
      simp only [d17733, d183708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17734 q = 1) (hb : d181811 q = 1) : d183709 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17734, d183709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17734, d183709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17741 q = 1) (hb : d181811 q = 1) : d183716 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17741, d183716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41163 q ha hb
    | true =>
      simp only [d17741, d183716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17742 q = 1) (hb : d181811 q = 1) : d183717 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17742, d183717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17742, d183717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17743 q = 1) (hb : d181811 q = 1) : d183718 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17743, d183718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17743, d183718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17744 q = 1) (hb : d181811 q = 1) : d183719 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17744, d183719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17744, d183719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17745 q = 1) (hb : d181811 q = 1) : d183720 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17745, d183720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17745, d183720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17746 q = 1) (hb : d181811 q = 1) : d183721 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17746, d183721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17746, d183721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41172 (p : Pattern) (ha : d17781 p = 1) (hb : d181811 p = 1) : d183727 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17733 q = 1) (hb : d181811 q = 1) : d183708 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17733, d183708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41169 q ha hb
    | true =>
      simp only [d17733, d183708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17734 q = 1) (hb : d181811 q = 1) : d183709 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17734, d183709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17734, d183709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17778 q = 1) (hb : d181811 q = 1) : d183724 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17778, d183724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17778, d183724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17779 q = 1) (hb : d181811 q = 1) : d183725 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17779, d183725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17779, d183725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17780 q = 1) (hb : d181811 q = 1) : d183726 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17780, d183726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17780, d183726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17781 q = 1) (hb : d181811 q = 1) : d183727 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17781, d183727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17781, d183727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41173 (p : Pattern) (ha : d129332 p = 1) (hb : d181811 p = 1) : d183733 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17747 q = 1) (hb : d181811 q = 1) : d183722 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17747, d183722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41170 q ha hb
    | true =>
      simp only [d17747, d183722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41171 q ha hb
  have h2 (q : Pattern) (ha : d129328 q = 1) (hb : d181811 q = 1) : d183723 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129328, d183723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129328, d183723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17782 q = 1) (hb : d181811 q = 1) : d183728 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17782, d183728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41172 q ha hb
    | true =>
      simp only [d17782, d183728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17783 q = 1) (hb : d181811 q = 1) : d183729 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17783, d183729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17783, d183729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129329 q = 1) (hb : d181811 q = 1) : d183730 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129329, d183730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129329, d183730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129330 q = 1) (hb : d181811 q = 1) : d183731 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129330, d183731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129330, d183731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129331 q = 1) (hb : d181811 q = 1) : d183732 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129331, d183732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129331, d183732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129332 q = 1) (hb : d181811 q = 1) : d183733 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129332, d183733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129332, d183733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41174 (p : Pattern) (ha : d129338 p = 1) (hb : d181811 p = 1) : d183750 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129333 q = 1) (hb : d181811 q = 1) : d183734 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129333, d183734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129333, d183734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41173 q ha hb
  have h2 (q : Pattern) (ha : d17799 q = 1) (hb : d181811 q = 1) : d183745 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17799, d183745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17799, d183745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41165 q ha hb
  have h3 (q : Pattern) (ha : d129334 q = 1) (hb : d181811 q = 1) : d183746 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129334, d183746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129334, d183746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129335 q = 1) (hb : d181811 q = 1) : d183747 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129335, d183747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129335, d183747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129336 q = 1) (hb : d181811 q = 1) : d183748 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129336, d183748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129336, d183748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129337 q = 1) (hb : d181811 q = 1) : d183749 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129337, d183749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129337, d183749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129338 q = 1) (hb : d181811 q = 1) : d183750 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129338, d183750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129338, d183750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41175 (p : Pattern) (ha : d129344 p = 1) (hb : d181811 p = 1) : d183756 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129339 q = 1) (hb : d181811 q = 1) : d183751 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129339, d183751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129339, d183751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41174 q ha hb
  have h2 (q : Pattern) (ha : d129340 q = 1) (hb : d181811 q = 1) : d183752 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129340, d183752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129340, d183752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129341 q = 1) (hb : d181811 q = 1) : d183753 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129341, d183753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129341, d183753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129342 q = 1) (hb : d181811 q = 1) : d183754 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129342, d183754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129342, d183754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129343 q = 1) (hb : d181811 q = 1) : d183755 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129343, d183755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129343, d183755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129344 q = 1) (hb : d181811 q = 1) : d183756 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129344, d183756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129344, d183756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41176 (p : Pattern) (ha : d17835 p = 1) (hb : d181811 p = 1) : d183781 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d412 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d102052 q = 1) : d319 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d413 q = 1) (hb : d181810 q = 1) : d9377 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d181810, d9377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d413, d181810, d9377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17643 q = 1) (hb : d181811 q = 1) : d183635 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17643, d181811, d183635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17643, d181811, d183635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17644 q = 1) (hb : d181811 q = 1) : d183636 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17644, d183636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17644, d183636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d971 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d751 q = 1) (hb : d102052 q = 1) : d751 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d972 q = 1) (hb : d181810 q = 1) : d9604 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d181810, d9604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d972, d181810, d9604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17821 q = 1) (hb : d181811 q = 1) : d183767 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17821, d181811, d183767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17821, d181811, d183767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d17822 q = 1) (hb : d181811 q = 1) : d183768 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17822, d183768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17822, d183768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d17834 q = 1) (hb : d181811 q = 1) : d183780 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17834, d183780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17834, d183780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17828 q = 1) (hb : d181811 q = 1) : d183774 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17828, d183774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17828, d183774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d17835 q = 1) (hb : d181811 q = 1) : d183781 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17835, d183781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17835, d183781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro41177 (p : Pattern) (ha : d17839 p = 1) (hb : d181811 p = 1) : d183785 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d971 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d751 q = 1) (hb : d102052 q = 1) : d751 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d972 q = 1) (hb : d181810 q = 1) : d9604 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d181810, d9604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d972, d181810, d9604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17821 q = 1) (hb : d181811 q = 1) : d183767 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17821, d181811, d183767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17821, d181811, d183767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17822 q = 1) (hb : d181811 q = 1) : d183768 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17822, d183768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17822, d183768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17828 q = 1) (hb : d181811 q = 1) : d183774 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17828, d183774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17828, d183774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d17839 q = 1) (hb : d181811 q = 1) : d183785 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17839, d183785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17839, d183785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro41178 (p : Pattern) (ha : d17858 p = 1) (hb : d181811 p = 1) : d183804 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17840 q = 1) (hb : d181811 q = 1) : d183786 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17840, d183786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41176 q ha hb
    | true =>
      simp only [d17840, d183786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41177 q ha hb
  have h2 (q : Pattern) (ha : d17841 q = 1) (hb : d181811 q = 1) : d183787 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17841, d183787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17841, d183787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17842 q = 1) (hb : d181811 q = 1) : d183788 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17842, d183788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17842, d183788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17848 q = 1) (hb : d181811 q = 1) : d183794 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17848, d183794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17848, d183794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17857 q = 1) (hb : d181811 q = 1) : d183803 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17857, d183803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17857, d183803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17858 q = 1) (hb : d181811 q = 1) : d183804 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17858, d183804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17858, d183804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41179 (p : Pattern) (ha : d17921 p = 1) (hb : d181811 p = 1) : d183827 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17859 q = 1) (hb : d181811 q = 1) : d183805 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17859, d183805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41178 q ha hb
    | true =>
      simp only [d17859, d183805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17860 q = 1) (hb : d181811 q = 1) : d183806 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17860, d183806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17860, d183806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17918 q = 1) (hb : d181811 q = 1) : d183824 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17918, d183824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17918, d183824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17919 q = 1) (hb : d181811 q = 1) : d183825 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17919, d183825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17919, d183825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17920 q = 1) (hb : d181811 q = 1) : d183826 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17920, d183826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17920, d183826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17921 q = 1) (hb : d181811 q = 1) : d183827 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17921, d183827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17921, d183827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41180 (p : Pattern) (ha : d17927 p = 1) (hb : d181811 p = 1) : d183833 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17922 q = 1) (hb : d181811 q = 1) : d183828 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17922, d183828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41179 q ha hb
    | true =>
      simp only [d17922, d183828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17923 q = 1) (hb : d181811 q = 1) : d183829 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17923, d183829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17923, d183829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17924 q = 1) (hb : d181811 q = 1) : d183830 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17924, d183830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17924, d183830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17925 q = 1) (hb : d181811 q = 1) : d183831 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17925, d183831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17925, d183831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17926 q = 1) (hb : d181811 q = 1) : d183832 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17926, d183832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17926, d183832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17927 q = 1) (hb : d181811 q = 1) : d183833 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17927, d183833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17927, d183833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41181 (p : Pattern) (ha : d17820 p = 1) (hb : d181811 p = 1) : d183766 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d834 q = 1) (hb : d102052 q = 1) : d834 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d966 q = 1) (hb : d181810 q = 1) : d9576 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d966, d181810, d9576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d966, d181810, d9576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17812 q = 1) (hb : d181811 q = 1) : d183758 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17812, d181811, d183758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17812, d181811, d183758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17813 q = 1) (hb : d181811 q = 1) : d183759 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17813, d183759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17813, d183759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d16356 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9587 q = 1) (hb : d102052 q = 1) : d9587 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d16357 q = 1) (hb : d181810 q = 1) : d9588 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16357, d181810, d9588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d16357, d181810, d9588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17814 q = 1) (hb : d181811 q = 1) : d183760 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17814, d181811, d183760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17814, d181811, d183760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d17815 q = 1) (hb : d181811 q = 1) : d183761 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17815, d183761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17815, d183761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d17816 q = 1) (hb : d181811 q = 1) : d183762 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17816, d183762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17816, d183762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d14644 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d9597 q = 1) (hb : d102052 q = 1) : d9597 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d14645 q = 1) (hb : d181810 q = 1) : d9598 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14645, d181810, d9598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d14645, d181810, d9598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17817 q = 1) (hb : d181811 q = 1) : d183763 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17817, d181811, d183763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d17817, d181811, d183763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h17 (q : Pattern) (ha : d17818 q = 1) (hb : d181811 q = 1) : d183764 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17818, d183764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17818, d183764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d12858 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d9468 q = 1) (hb : d102052 q = 1) : d9468 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d12859 q = 1) (hb : d181810 q = 1) : d9469 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d181810, d9469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d12859, d181810, d9469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d17714 q = 1) (hb : d181811 q = 1) : d183689 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17714, d181811, d183689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d17714, d181811, d183689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h22 (q : Pattern) (ha : d17715 q = 1) (hb : d181811 q = 1) : d183690 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17715, d183690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d17715, d183690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h23 (q : Pattern) (ha : d17819 q = 1) (hb : d181811 q = 1) : d183765 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17819, d183765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d17819, d183765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d17820 q = 1) (hb : d181811 q = 1) : d183766 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17820, d183766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17820, d183766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro41182 (p : Pattern) (ha : d17824 p = 1) (hb : d181811 p = 1) : d183770 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d659 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d543 q = 1) (hb : d102052 q = 1) : d543 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d660 q = 1) (hb : d181810 q = 1) : d9449 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, d181810, d9449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d660, d181810, d9449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17709 q = 1) (hb : d181811 q = 1) : d183684 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17709, d181811, d183684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17709, d181811, d183684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17710 q = 1) (hb : d181811 q = 1) : d183685 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17710, d183685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17710, d183685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d16156 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9458 q = 1) (hb : d102052 q = 1) : d9458 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d16157 q = 1) (hb : d181810 q = 1) : d9459 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16157, d181810, d9459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d16157, d181810, d9459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17711 q = 1) (hb : d181811 q = 1) : d183686 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17711, d181811, d183686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17711, d181811, d183686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d17712 q = 1) (hb : d181811 q = 1) : d183687 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17712, d183687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17712, d183687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d17713 q = 1) (hb : d181811 q = 1) : d183688 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17713, d183688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17713, d183688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d12858 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d9468 q = 1) (hb : d102052 q = 1) : d9468 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d12859 q = 1) (hb : d181810 q = 1) : d9469 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d181810, d9469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d12859, d181810, d9469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17714 q = 1) (hb : d181811 q = 1) : d183689 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17714, d181811, d183689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d17714, d181811, d183689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h17 (q : Pattern) (ha : d17715 q = 1) (hb : d181811 q = 1) : d183690 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17715, d183690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17715, d183690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d971 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d751 q = 1) (hb : d102052 q = 1) : d751 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d972 q = 1) (hb : d181810 q = 1) : d9604 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d181810, d9604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d972, d181810, d9604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d17821 q = 1) (hb : d181811 q = 1) : d183767 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17821, d181811, d183767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d17821, d181811, d183767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h22 (q : Pattern) (ha : d17822 q = 1) (hb : d181811 q = 1) : d183768 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17822, d183768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d17822, d183768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h23 (q : Pattern) (ha : d17823 q = 1) (hb : d181811 q = 1) : d183769 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17823, d183769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d17823, d183769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d17824 q = 1) (hb : d181811 q = 1) : d183770 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17824, d183770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17824, d183770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro41183 (p : Pattern) (ha : d17829 p = 1) (hb : d181811 p = 1) : d183775 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12858 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9468 q = 1) (hb : d102052 q = 1) : d9468 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12859 q = 1) (hb : d181810 q = 1) : d9469 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d181810, d9469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12859, d181810, d9469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17714 q = 1) (hb : d181811 q = 1) : d183689 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17714, d181811, d183689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17714, d181811, d183689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17715 q = 1) (hb : d181811 q = 1) : d183690 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17715, d183690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17715, d183690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d971 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d751 q = 1) (hb : d102052 q = 1) : d751 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d972 q = 1) (hb : d181810 q = 1) : d9604 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d181810, d9604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d972, d181810, d9604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17821 q = 1) (hb : d181811 q = 1) : d183767 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17821, d181811, d183767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17821, d181811, d183767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d17822 q = 1) (hb : d181811 q = 1) : d183768 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17822, d183768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17822, d183768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d17823 q = 1) (hb : d181811 q = 1) : d183769 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17823, d183769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17823, d183769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17828 q = 1) (hb : d181811 q = 1) : d183774 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17828, d183774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17828, d183774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d17829 q = 1) (hb : d181811 q = 1) : d183775 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17829, d183775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17829, d183775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro41184 (p : Pattern) (ha : d17845 p = 1) (hb : d181811 p = 1) : d183791 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17825 q = 1) (hb : d181811 q = 1) : d183771 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17825, d183771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41181 q ha hb
    | true =>
      simp only [d17825, d183771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41182 q ha hb
  have h2 (q : Pattern) (ha : d17826 q = 1) (hb : d181811 q = 1) : d183772 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17826, d183772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17826, d183772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17827 q = 1) (hb : d181811 q = 1) : d183773 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17827, d183773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17827, d183773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17830 q = 1) (hb : d181811 q = 1) : d183776 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17830, d183776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41182 q ha hb
    | true =>
      simp only [d17830, d183776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41183 q ha hb
  have h5 (q : Pattern) (ha : d17831 q = 1) (hb : d181811 q = 1) : d183777 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17831, d183777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17831, d183777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17832 q = 1) (hb : d181811 q = 1) : d183778 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17832, d183778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17832, d183778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17833 q = 1) (hb : d181811 q = 1) : d183779 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17833, d183779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17833, d183779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17836 q = 1) (hb : d181811 q = 1) : d183782 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17836, d183782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41182 q ha hb
    | true =>
      simp only [d17836, d183782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41176 q ha hb
  have h9 (q : Pattern) (ha : d17837 q = 1) (hb : d181811 q = 1) : d183783 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17837, d183783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17837, d183783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17838 q = 1) (hb : d181811 q = 1) : d183784 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17838, d183784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17838, d183784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17840 q = 1) (hb : d181811 q = 1) : d183786 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17840, d183786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41176 q ha hb
    | true =>
      simp only [d17840, d183786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41177 q ha hb
  have h12 (q : Pattern) (ha : d17841 q = 1) (hb : d181811 q = 1) : d183787 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17841, d183787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17841, d183787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17842 q = 1) (hb : d181811 q = 1) : d183788 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17842, d183788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17842, d183788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17843 q = 1) (hb : d181811 q = 1) : d183789 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17843, d183789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17843, d183789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17844 q = 1) (hb : d181811 q = 1) : d183790 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17844, d183790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17844, d183790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17845 q = 1) (hb : d181811 q = 1) : d183791 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17845, d183791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d17845, d183791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro41185 (p : Pattern) (ha : d17850 p = 1) (hb : d181811 p = 1) : d183796 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17836 q = 1) (hb : d181811 q = 1) : d183782 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17836, d183782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41182 q ha hb
    | true =>
      simp only [d17836, d183782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41176 q ha hb
  have h2 (q : Pattern) (ha : d17837 q = 1) (hb : d181811 q = 1) : d183783 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17837, d183783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17837, d183783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17838 q = 1) (hb : d181811 q = 1) : d183784 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17838, d183784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17838, d183784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17840 q = 1) (hb : d181811 q = 1) : d183786 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17840, d183786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41176 q ha hb
    | true =>
      simp only [d17840, d183786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41177 q ha hb
  have h5 (q : Pattern) (ha : d17841 q = 1) (hb : d181811 q = 1) : d183787 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17841, d183787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17841, d183787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17842 q = 1) (hb : d181811 q = 1) : d183788 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17842, d183788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17842, d183788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17843 q = 1) (hb : d181811 q = 1) : d183789 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17843, d183789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17843, d183789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17848 q = 1) (hb : d181811 q = 1) : d183794 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17848, d183794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17848, d183794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17849 q = 1) (hb : d181811 q = 1) : d183795 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17849, d183795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17849, d183795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17850 q = 1) (hb : d181811 q = 1) : d183796 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17850, d183796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17850, d183796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro41186 (p : Pattern) (ha : d17856 p = 1) (hb : d181811 p = 1) : d183802 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17846 q = 1) (hb : d181811 q = 1) : d183792 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17846, d183792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41184 q ha hb
    | true =>
      simp only [d17846, d183792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17847 q = 1) (hb : d181811 q = 1) : d183793 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17847, d183793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17847, d183793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17851 q = 1) (hb : d181811 q = 1) : d183797 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17851, d183797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41185 q ha hb
    | true =>
      simp only [d17851, d183797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17852 q = 1) (hb : d181811 q = 1) : d183798 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17852, d183798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17852, d183798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17853 q = 1) (hb : d181811 q = 1) : d183799 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17853, d183799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17853, d183799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17854 q = 1) (hb : d181811 q = 1) : d183800 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17854, d183800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17854, d183800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17855 q = 1) (hb : d181811 q = 1) : d183801 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17855, d183801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17855, d183801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17856 q = 1) (hb : d181811 q = 1) : d183802 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17856, d183802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17856, d183802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41187 (p : Pattern) (ha : d17864 p = 1) (hb : d181811 p = 1) : d183810 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17851 q = 1) (hb : d181811 q = 1) : d183797 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17851, d183797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41185 q ha hb
    | true =>
      simp only [d17851, d183797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17852 q = 1) (hb : d181811 q = 1) : d183798 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17852, d183798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17852, d183798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17859 q = 1) (hb : d181811 q = 1) : d183805 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17859, d183805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41178 q ha hb
    | true =>
      simp only [d17859, d183805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17860 q = 1) (hb : d181811 q = 1) : d183806 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17860, d183806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17860, d183806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17861 q = 1) (hb : d181811 q = 1) : d183807 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17861, d183807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17861, d183807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17862 q = 1) (hb : d181811 q = 1) : d183808 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17862, d183808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17862, d183808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17863 q = 1) (hb : d181811 q = 1) : d183809 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17863, d183809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17863, d183809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17864 q = 1) (hb : d181811 q = 1) : d183810 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17864, d183810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17864, d183810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41188 (p : Pattern) (ha : d17910 p = 1) (hb : d181811 p = 1) : d183816 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17851 q = 1) (hb : d181811 q = 1) : d183797 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17851, d183797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41185 q ha hb
    | true =>
      simp only [d17851, d183797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17852 q = 1) (hb : d181811 q = 1) : d183798 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17852, d183798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17852, d183798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17907 q = 1) (hb : d181811 q = 1) : d183813 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17907, d183813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17907, d183813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17908 q = 1) (hb : d181811 q = 1) : d183814 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17908, d183814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17908, d183814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17909 q = 1) (hb : d181811 q = 1) : d183815 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17909, d183815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17909, d183815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17910 q = 1) (hb : d181811 q = 1) : d183816 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17910, d183816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17910, d183816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41189 (p : Pattern) (ha : d129350 p = 1) (hb : d181811 p = 1) : d183822 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17865 q = 1) (hb : d181811 q = 1) : d183811 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17865, d183811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41186 q ha hb
    | true =>
      simp only [d17865, d183811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41187 q ha hb
  have h2 (q : Pattern) (ha : d129346 q = 1) (hb : d181811 q = 1) : d183812 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129346, d183812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129346, d183812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17911 q = 1) (hb : d181811 q = 1) : d183817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17911, d183817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41188 q ha hb
    | true =>
      simp only [d17911, d183817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17912 q = 1) (hb : d181811 q = 1) : d183818 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17912, d183818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17912, d183818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129347 q = 1) (hb : d181811 q = 1) : d183819 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129347, d183819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129347, d183819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129348 q = 1) (hb : d181811 q = 1) : d183820 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129348, d183820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129348, d183820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129349 q = 1) (hb : d181811 q = 1) : d183821 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129349, d183821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129349, d183821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129350 q = 1) (hb : d181811 q = 1) : d183822 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129350, d183822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129350, d183822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41190 (p : Pattern) (ha : d129356 p = 1) (hb : d181811 p = 1) : d183839 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129351 q = 1) (hb : d181811 q = 1) : d183823 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129351, d183823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129351, d183823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41189 q ha hb
  have h2 (q : Pattern) (ha : d17928 q = 1) (hb : d181811 q = 1) : d183834 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17928, d183834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17928, d183834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41180 q ha hb
  have h3 (q : Pattern) (ha : d129352 q = 1) (hb : d181811 q = 1) : d183835 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129352, d183835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129352, d183835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129353 q = 1) (hb : d181811 q = 1) : d183836 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129353, d183836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129353, d183836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129354 q = 1) (hb : d181811 q = 1) : d183837 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129354, d183837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129354, d183837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129355 q = 1) (hb : d181811 q = 1) : d183838 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129355, d183838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129355, d183838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129356 q = 1) (hb : d181811 q = 1) : d183839 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129356, d183839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129356, d183839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41191 (p : Pattern) (ha : d129362 p = 1) (hb : d181811 p = 1) : d183845 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129357 q = 1) (hb : d181811 q = 1) : d183840 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129357, d183840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129357, d183840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41190 q ha hb
  have h2 (q : Pattern) (ha : d129358 q = 1) (hb : d181811 q = 1) : d183841 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129358, d183841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129358, d183841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129359 q = 1) (hb : d181811 q = 1) : d183842 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129359, d183842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129359, d183842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129360 q = 1) (hb : d181811 q = 1) : d183843 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129360, d183843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129360, d183843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129361 q = 1) (hb : d181811 q = 1) : d183844 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129361, d183844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129361, d183844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129362 q = 1) (hb : d181811 q = 1) : d183845 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129362, d183845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129362, d183845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41192 (p : Pattern) (ha : d17979 p = 1) (hb : d181811 p = 1) : d183885 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1385 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1110 q = 1) (hb : d102052 q = 1) : d1110 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1386 q = 1) (hb : d181810 q = 1) : d9826 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1386, d181810, d9826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1386, d181810, d9826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17974 q = 1) (hb : d181811 q = 1) : d183880 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17974, d181811, d183880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17974, d181811, d183880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17975 q = 1) (hb : d181811 q = 1) : d183881 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17975, d183881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17975, d183881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1391 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1121 q = 1) (hb : d102052 q = 1) : d1121 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1392 q = 1) (hb : d181810 q = 1) : d9829 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d181810, d9829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d1392, d181810, d9829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17976 q = 1) (hb : d181811 q = 1) : d183882 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17976, d181811, d183882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17976, d181811, d183882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d17977 q = 1) (hb : d181811 q = 1) : d183883 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17977, d183883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17977, d183883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d17978 q = 1) (hb : d181811 q = 1) : d183884 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17978, d183884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17978, d183884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d15004 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d9800 q = 1) (hb : d102052 q = 1) : d9800 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d15005 q = 1) (hb : d181810 q = 1) : d9801 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15005, d181810, d9801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d15005, d181810, d9801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17958 q = 1) (hb : d181811 q = 1) : d183864 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17958, d181811, d183864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d17958, d181811, d183864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h17 (q : Pattern) (ha : d17959 q = 1) (hb : d181811 q = 1) : d183865 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17959, d183865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17959, d183865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d17968 q = 1) (hb : d181811 q = 1) : d183874 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17968, d183874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d17968, d183874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h19 (q : Pattern) (ha : d17979 q = 1) (hb : d181811 q = 1) : d183885 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17979, d183885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17979, d183885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro41193 (p : Pattern) (ha : d18008 p = 1) (hb : d181811 p = 1) : d183914 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1391 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1121 q = 1) (hb : d102052 q = 1) : d1121 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1392 q = 1) (hb : d181810 q = 1) : d9829 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d181810, d9829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1392, d181810, d9829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17976 q = 1) (hb : d181811 q = 1) : d183882 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17976, d181811, d183882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17976, d181811, d183882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17977 q = 1) (hb : d181811 q = 1) : d183883 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17977, d183883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17977, d183883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18007 q = 1) (hb : d181811 q = 1) : d183913 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18007, d183913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18007, d183913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d15019 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d9844 q = 1) (hb : d102052 q = 1) : d9844 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15020 q = 1) (hb : d181810 q = 1) : d9845 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15020, d181810, d9845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d15020, d181810, d9845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17986 q = 1) (hb : d181811 q = 1) : d183892 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17986, d181811, d183892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17986, d181811, d183892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d17987 q = 1) (hb : d181811 q = 1) : d183893 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17987, d183893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17987, d183893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h13 (q : Pattern) (ha : d17988 q = 1) (hb : d181811 q = 1) : d183894 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17988, d183894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17988, d183894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d18008 q = 1) (hb : d181811 q = 1) : d183914 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18008, d183914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18008, d183914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro41194 (p : Pattern) (ha : d18014 p = 1) (hb : d181811 p = 1) : d183920 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18009 q = 1) (hb : d181811 q = 1) : d183915 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18009, d183915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41192 q ha hb
    | true =>
      simp only [d18009, d183915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41193 q ha hb
  have h2 (q : Pattern) (ha : d18010 q = 1) (hb : d181811 q = 1) : d183916 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18010, d183916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18010, d183916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18011 q = 1) (hb : d181811 q = 1) : d183917 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18011, d183917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18011, d183917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18012 q = 1) (hb : d181811 q = 1) : d183918 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18012, d183918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18012, d183918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18013 q = 1) (hb : d181811 q = 1) : d183919 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18013, d183919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18013, d183919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18014 q = 1) (hb : d181811 q = 1) : d183920 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18014, d183920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18014, d183920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41195 (p : Pattern) (ha : d18101 p = 1) (hb : d181811 p = 1) : d183952 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18015 q = 1) (hb : d181811 q = 1) : d183921 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18015, d183921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41194 q ha hb
    | true =>
      simp only [d18015, d183921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18016 q = 1) (hb : d181811 q = 1) : d183922 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18016, d183922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18016, d183922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18098 q = 1) (hb : d181811 q = 1) : d183949 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18098, d183949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18098, d183949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18099 q = 1) (hb : d181811 q = 1) : d183950 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18099, d183950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18099, d183950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18100 q = 1) (hb : d181811 q = 1) : d183951 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18100, d183951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18100, d183951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18101 q = 1) (hb : d181811 q = 1) : d183952 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18101, d183952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18101, d183952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41196 (p : Pattern) (ha : d18107 p = 1) (hb : d181811 p = 1) : d183958 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18102 q = 1) (hb : d181811 q = 1) : d183953 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18102, d183953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41195 q ha hb
    | true =>
      simp only [d18102, d183953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18103 q = 1) (hb : d181811 q = 1) : d183954 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18103, d183954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18103, d183954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18104 q = 1) (hb : d181811 q = 1) : d183955 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18104, d183955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18104, d183955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18105 q = 1) (hb : d181811 q = 1) : d183956 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18105, d183956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18105, d183956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18106 q = 1) (hb : d181811 q = 1) : d183957 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18106, d183957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18106, d183957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18107 q = 1) (hb : d181811 q = 1) : d183958 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18107, d183958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18107, d183958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41197 (p : Pattern) (ha : d17952 p = 1) (hb : d181811 p = 1) : d183858 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1376 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1210 q = 1) (hb : d102052 q = 1) : d1210 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1377 q = 1) (hb : d181810 q = 1) : d9746 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1377, d181810, d9746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1377, d181810, d9746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17942 q = 1) (hb : d181811 q = 1) : d183848 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17942, d181811, d183848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17942, d181811, d183848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17943 q = 1) (hb : d181811 q = 1) : d183849 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17943, d183849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17943, d183849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d16649 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9753 q = 1) (hb : d102052 q = 1) : d9753 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d16650 q = 1) (hb : d181810 q = 1) : d9754 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16650, d181810, d9754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d16650, d181810, d9754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17944 q = 1) (hb : d181811 q = 1) : d183850 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17944, d181811, d183850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17944, d181811, d183850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d17945 q = 1) (hb : d181811 q = 1) : d183851 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17945, d183851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17945, d183851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d17946 q = 1) (hb : d181811 q = 1) : d183852 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17946, d183852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17946, d183852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d14987 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d9763 q = 1) (hb : d102052 q = 1) : d9763 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d14988 q = 1) (hb : d181810 q = 1) : d9764 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14988, d181810, d9764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d14988, d181810, d9764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17947 q = 1) (hb : d181811 q = 1) : d183853 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17947, d181811, d183853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d17947, d181811, d183853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h17 (q : Pattern) (ha : d17948 q = 1) (hb : d181811 q = 1) : d183854 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17948, d183854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17948, d183854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d14994 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d9778 q = 1) (hb : d102052 q = 1) : d9778 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d14995 q = 1) (hb : d181810 q = 1) : d9779 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14995, d181810, d9779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d14995, d181810, d9779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d17949 q = 1) (hb : d181811 q = 1) : d183855 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17949, d181811, d183855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d17949, d181811, d183855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h22 (q : Pattern) (ha : d17950 q = 1) (hb : d181811 q = 1) : d183856 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17950, d183856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d17950, d183856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h23 (q : Pattern) (ha : d17951 q = 1) (hb : d181811 q = 1) : d183857 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17951, d183857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d17951, d183857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d17952 q = 1) (hb : d181811 q = 1) : d183858 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17952, d183858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17952, d183858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro41198 (p : Pattern) (ha : d17961 p = 1) (hb : d181811 p = 1) : d183867 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1380 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1100 q = 1) (hb : d102052 q = 1) : d1100 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1381 q = 1) (hb : d181810 q = 1) : d9785 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1381, d181810, d9785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1381, d181810, d9785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17953 q = 1) (hb : d181811 q = 1) : d183859 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17953, d181811, d183859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17953, d181811, d183859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17954 q = 1) (hb : d181811 q = 1) : d183860 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17954, d183860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17954, d183860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d16656 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9789 q = 1) (hb : d102052 q = 1) : d9789 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d16657 q = 1) (hb : d181810 q = 1) : d9790 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16657, d181810, d9790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d16657, d181810, d9790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17955 q = 1) (hb : d181811 q = 1) : d183861 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17955, d181811, d183861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17955, d181811, d183861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d17956 q = 1) (hb : d181811 q = 1) : d183862 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17956, d183862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17956, d183862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d17957 q = 1) (hb : d181811 q = 1) : d183863 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17957, d183863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17957, d183863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d14994 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d9778 q = 1) (hb : d102052 q = 1) : d9778 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d14995 q = 1) (hb : d181810 q = 1) : d9779 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14995, d181810, d9779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d14995, d181810, d9779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17949 q = 1) (hb : d181811 q = 1) : d183855 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17949, d181811, d183855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d17949, d181811, d183855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h17 (q : Pattern) (ha : d17950 q = 1) (hb : d181811 q = 1) : d183856 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17950, d183856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17950, d183856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d15004 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d9800 q = 1) (hb : d102052 q = 1) : d9800 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d15005 q = 1) (hb : d181810 q = 1) : d9801 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15005, d181810, d9801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d15005, d181810, d9801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d17958 q = 1) (hb : d181811 q = 1) : d183864 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17958, d181811, d183864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d17958, d181811, d183864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h22 (q : Pattern) (ha : d17959 q = 1) (hb : d181811 q = 1) : d183865 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17959, d183865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d17959, d183865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h23 (q : Pattern) (ha : d17960 q = 1) (hb : d181811 q = 1) : d183866 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17960, d183866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d17960, d183866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d17961 q = 1) (hb : d181811 q = 1) : d183867 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17961, d183867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17961, d183867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro41199 (p : Pattern) (ha : d17969 p = 1) (hb : d181811 p = 1) : d183875 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13160 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9814 q = 1) (hb : d102052 q = 1) : d9814 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13161 q = 1) (hb : d181810 q = 1) : d9815 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13161, d181810, d9815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13161, d181810, d9815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17965 q = 1) (hb : d181811 q = 1) : d183871 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17965, d181811, d183871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17965, d181811, d183871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17966 q = 1) (hb : d181811 q = 1) : d183872 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17966, d183872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17966, d183872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d15004 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9800 q = 1) (hb : d102052 q = 1) : d9800 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15005 q = 1) (hb : d181810 q = 1) : d9801 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15005, d181810, d9801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d15005, d181810, d9801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17958 q = 1) (hb : d181811 q = 1) : d183864 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17958, d181811, d183864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17958, d181811, d183864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d17959 q = 1) (hb : d181811 q = 1) : d183865 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17959, d183865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17959, d183865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d17967 q = 1) (hb : d181811 q = 1) : d183873 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17967, d183873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17967, d183873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17968 q = 1) (hb : d181811 q = 1) : d183874 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17968, d183874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17968, d183874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d17969 q = 1) (hb : d181811 q = 1) : d183875 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17969, d183875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17969, d183875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro41200 (p : Pattern) (ha : d17989 p = 1) (hb : d181811 p = 1) : d183895 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6350 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5018 q = 1) (hb : d102052 q = 1) : d5018 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6351 q = 1) (hb : d181810 q = 1) : d9837 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6351, d181810, d9837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6351, d181810, d9837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17983 q = 1) (hb : d181811 q = 1) : d183889 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17983, d181811, d183889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17983, d181811, d183889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17984 q = 1) (hb : d181811 q = 1) : d183890 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17984, d183890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17984, d183890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17985 q = 1) (hb : d181811 q = 1) : d183891 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17985, d183891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17985, d183891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d15019 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d9844 q = 1) (hb : d102052 q = 1) : d9844 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15020 q = 1) (hb : d181810 q = 1) : d9845 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15020, d181810, d9845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d15020, d181810, d9845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17986 q = 1) (hb : d181811 q = 1) : d183892 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17986, d181811, d183892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17986, d181811, d183892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d17987 q = 1) (hb : d181811 q = 1) : d183893 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17987, d183893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17987, d183893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h13 (q : Pattern) (ha : d17988 q = 1) (hb : d181811 q = 1) : d183894 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17988, d183894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17988, d183894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d17989 q = 1) (hb : d181811 q = 1) : d183895 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17989, d183895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17989, d183895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro41201 (p : Pattern) (ha : d17995 p = 1) (hb : d181811 p = 1) : d183901 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17962 q = 1) (hb : d181811 q = 1) : d183868 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17962, d183868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41197 q ha hb
    | true =>
      simp only [d17962, d183868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41198 q ha hb
  have h2 (q : Pattern) (ha : d17963 q = 1) (hb : d181811 q = 1) : d183869 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17963, d183869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17963, d183869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17964 q = 1) (hb : d181811 q = 1) : d183870 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17964, d183870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17964, d183870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17970 q = 1) (hb : d181811 q = 1) : d183876 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17970, d183876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41198 q ha hb
    | true =>
      simp only [d17970, d183876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41199 q ha hb
  have h5 (q : Pattern) (ha : d17971 q = 1) (hb : d181811 q = 1) : d183877 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17971, d183877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17971, d183877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17972 q = 1) (hb : d181811 q = 1) : d183878 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17972, d183878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17972, d183878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17973 q = 1) (hb : d181811 q = 1) : d183879 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17973, d183879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17973, d183879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17980 q = 1) (hb : d181811 q = 1) : d183886 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17980, d183886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41198 q ha hb
    | true =>
      simp only [d17980, d183886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41192 q ha hb
  have h9 (q : Pattern) (ha : d17981 q = 1) (hb : d181811 q = 1) : d183887 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17981, d183887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17981, d183887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17982 q = 1) (hb : d181811 q = 1) : d183888 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17982, d183888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17982, d183888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17990 q = 1) (hb : d181811 q = 1) : d183896 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17990, d183896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41192 q ha hb
    | true =>
      simp only [d17990, d183896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41200 q ha hb
  have h12 (q : Pattern) (ha : d17991 q = 1) (hb : d181811 q = 1) : d183897 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17991, d183897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17991, d183897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17992 q = 1) (hb : d181811 q = 1) : d183898 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17992, d183898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17992, d183898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17993 q = 1) (hb : d181811 q = 1) : d183899 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17993, d183899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17993, d183899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17994 q = 1) (hb : d181811 q = 1) : d183900 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17994, d183900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17994, d183900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17995 q = 1) (hb : d181811 q = 1) : d183901 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17995, d183901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d17995, d183901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro41202 (p : Pattern) (ha : d18000 p = 1) (hb : d181811 p = 1) : d183906 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17980 q = 1) (hb : d181811 q = 1) : d183886 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17980, d183886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41198 q ha hb
    | true =>
      simp only [d17980, d183886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41192 q ha hb
  have h2 (q : Pattern) (ha : d17981 q = 1) (hb : d181811 q = 1) : d183887 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17981, d183887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17981, d183887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17982 q = 1) (hb : d181811 q = 1) : d183888 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17982, d183888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17982, d183888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17990 q = 1) (hb : d181811 q = 1) : d183896 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17990, d183896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41192 q ha hb
    | true =>
      simp only [d17990, d183896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41200 q ha hb
  have h5 (q : Pattern) (ha : d17991 q = 1) (hb : d181811 q = 1) : d183897 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17991, d183897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17991, d183897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17992 q = 1) (hb : d181811 q = 1) : d183898 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17992, d183898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17992, d183898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17993 q = 1) (hb : d181811 q = 1) : d183899 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17993, d183899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17993, d183899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17998 q = 1) (hb : d181811 q = 1) : d183904 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17998, d183904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17998, d183904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17999 q = 1) (hb : d181811 q = 1) : d183905 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17999, d183905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17999, d183905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18000 q = 1) (hb : d181811 q = 1) : d183906 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18000, d183906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18000, d183906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro41203 (p : Pattern) (ha : d18006 p = 1) (hb : d181811 p = 1) : d183912 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17996 q = 1) (hb : d181811 q = 1) : d183902 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17996, d183902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41201 q ha hb
    | true =>
      simp only [d17996, d183902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17997 q = 1) (hb : d181811 q = 1) : d183903 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17997, d183903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17997, d183903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18001 q = 1) (hb : d181811 q = 1) : d183907 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18001, d183907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41202 q ha hb
    | true =>
      simp only [d18001, d183907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18002 q = 1) (hb : d181811 q = 1) : d183908 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18002, d183908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18002, d183908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18003 q = 1) (hb : d181811 q = 1) : d183909 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18003, d183909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18003, d183909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18004 q = 1) (hb : d181811 q = 1) : d183910 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18004, d183910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18004, d183910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18005 q = 1) (hb : d181811 q = 1) : d183911 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18005, d183911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18005, d183911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18006 q = 1) (hb : d181811 q = 1) : d183912 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18006, d183912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18006, d183912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41204 (p : Pattern) (ha : d18020 p = 1) (hb : d181811 p = 1) : d183926 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18001 q = 1) (hb : d181811 q = 1) : d183907 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18001, d183907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41202 q ha hb
    | true =>
      simp only [d18001, d183907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18002 q = 1) (hb : d181811 q = 1) : d183908 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18002, d183908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18002, d183908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18015 q = 1) (hb : d181811 q = 1) : d183921 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18015, d183921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41194 q ha hb
    | true =>
      simp only [d18015, d183921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18016 q = 1) (hb : d181811 q = 1) : d183922 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18016, d183922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18016, d183922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18017 q = 1) (hb : d181811 q = 1) : d183923 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18017, d183923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18017, d183923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18018 q = 1) (hb : d181811 q = 1) : d183924 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18018, d183924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18018, d183924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18019 q = 1) (hb : d181811 q = 1) : d183925 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18019, d183925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18019, d183925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18020 q = 1) (hb : d181811 q = 1) : d183926 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18020, d183926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18020, d183926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41205 (p : Pattern) (ha : d18078 p = 1) (hb : d181811 p = 1) : d183929 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1391 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1121 q = 1) (hb : d102052 q = 1) : d1121 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1392 q = 1) (hb : d181810 q = 1) : d9829 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d181810, d9829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1392, d181810, d9829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17976 q = 1) (hb : d181811 q = 1) : d183882 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17976, d181811, d183882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17976, d181811, d183882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d17977 q = 1) (hb : d181811 q = 1) : d183883 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17977, d183883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17977, d183883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18007 q = 1) (hb : d181811 q = 1) : d183913 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18007, d183913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18007, d183913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d18078 q = 1) (hb : d181811 q = 1) : d183929 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18078, d183929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18078, d183929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro41206 (p : Pattern) (ha : d18084 p = 1) (hb : d181811 p = 1) : d183935 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17980 q = 1) (hb : d181811 q = 1) : d183886 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17980, d183886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41198 q ha hb
    | true =>
      simp only [d17980, d183886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41192 q ha hb
  have h2 (q : Pattern) (ha : d17981 q = 1) (hb : d181811 q = 1) : d183887 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17981, d183887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17981, d183887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17982 q = 1) (hb : d181811 q = 1) : d183888 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17982, d183888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17982, d183888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17990 q = 1) (hb : d181811 q = 1) : d183896 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17990, d183896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41192 q ha hb
    | true =>
      simp only [d17990, d183896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41200 q ha hb
  have h5 (q : Pattern) (ha : d17991 q = 1) (hb : d181811 q = 1) : d183897 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17991, d183897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17991, d183897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17992 q = 1) (hb : d181811 q = 1) : d183898 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17992, d183898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17992, d183898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17993 q = 1) (hb : d181811 q = 1) : d183899 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17993, d183899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17993, d183899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18079 q = 1) (hb : d181811 q = 1) : d183930 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18079, d183930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41192 q ha hb
    | true =>
      simp only [d18079, d183930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41205 q ha hb
  have h9 (q : Pattern) (ha : d18080 q = 1) (hb : d181811 q = 1) : d183931 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18080, d183931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18080, d183931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18081 q = 1) (hb : d181811 q = 1) : d183932 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18081, d183932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18081, d183932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18082 q = 1) (hb : d181811 q = 1) : d183933 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18082, d183933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18082, d183933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d18083 q = 1) (hb : d181811 q = 1) : d183934 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18083, d183934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18083, d183934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18084 q = 1) (hb : d181811 q = 1) : d183935 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18084, d183935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18084, d183935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro41207 (p : Pattern) (ha : d18090 p = 1) (hb : d181811 p = 1) : d183941 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18085 q = 1) (hb : d181811 q = 1) : d183936 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18085, d183936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41206 q ha hb
    | true =>
      simp only [d18085, d183936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18086 q = 1) (hb : d181811 q = 1) : d183937 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18086, d183937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18086, d183937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18087 q = 1) (hb : d181811 q = 1) : d183938 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18087, d183938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18087, d183938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18088 q = 1) (hb : d181811 q = 1) : d183939 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18088, d183939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18088, d183939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18089 q = 1) (hb : d181811 q = 1) : d183940 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18089, d183940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18089, d183940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18090 q = 1) (hb : d181811 q = 1) : d183941 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18090, d183941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18090, d183941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41208 (p : Pattern) (ha : d129369 p = 1) (hb : d181811 p = 1) : d183947 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18021 q = 1) (hb : d181811 q = 1) : d183927 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18021, d183927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41203 q ha hb
    | true =>
      simp only [d18021, d183927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41204 q ha hb
  have h2 (q : Pattern) (ha : d129365 q = 1) (hb : d181811 q = 1) : d183928 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129365, d183928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129365, d183928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d18091 q = 1) (hb : d181811 q = 1) : d183942 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18091, d183942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41207 q ha hb
    | true =>
      simp only [d18091, d183942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18092 q = 1) (hb : d181811 q = 1) : d183943 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18092, d183943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18092, d183943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129366 q = 1) (hb : d181811 q = 1) : d183944 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129366, d183944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129366, d183944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129367 q = 1) (hb : d181811 q = 1) : d183945 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129367, d183945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129367, d183945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129368 q = 1) (hb : d181811 q = 1) : d183946 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129368, d183946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129368, d183946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129369 q = 1) (hb : d181811 q = 1) : d183947 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129369, d183947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129369, d183947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41209 (p : Pattern) (ha : d129375 p = 1) (hb : d181811 p = 1) : d183964 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129370 q = 1) (hb : d181811 q = 1) : d183948 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129370, d183948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129370, d183948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41208 q ha hb
  have h2 (q : Pattern) (ha : d18108 q = 1) (hb : d181811 q = 1) : d183959 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18108, d183959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18108, d183959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41196 q ha hb
  have h3 (q : Pattern) (ha : d129371 q = 1) (hb : d181811 q = 1) : d183960 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129371, d183960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129371, d183960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129372 q = 1) (hb : d181811 q = 1) : d183961 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129372, d183961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129372, d183961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129373 q = 1) (hb : d181811 q = 1) : d183962 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129373, d183962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129373, d183962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129374 q = 1) (hb : d181811 q = 1) : d183963 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129374, d183963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129374, d183963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129375 q = 1) (hb : d181811 q = 1) : d183964 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129375, d183964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129375, d183964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41210 (p : Pattern) (ha : d129381 p = 1) (hb : d181811 p = 1) : d183970 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129376 q = 1) (hb : d181811 q = 1) : d183965 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129376, d183965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129376, d183965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41209 q ha hb
  have h2 (q : Pattern) (ha : d129377 q = 1) (hb : d181811 q = 1) : d183966 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129377, d183966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129377, d183966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129378 q = 1) (hb : d181811 q = 1) : d183967 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129378, d183967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129378, d183967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129379 q = 1) (hb : d181811 q = 1) : d183968 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129379, d183968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129379, d183968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129380 q = 1) (hb : d181811 q = 1) : d183969 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129380, d183969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129380, d183969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129381 q = 1) (hb : d181811 q = 1) : d183970 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129381, d183970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129381, d183970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41211 (p : Pattern) (ha : d18160 p = 1) (hb : d181811 p = 1) : d184011 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1862 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1570 q = 1) (hb : d102052 q = 1) : d1570 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1863 q = 1) (hb : d181810 q = 1) : d10111 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1863, d181810, d10111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1863, d181810, d10111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18155 q = 1) (hb : d181811 q = 1) : d184006 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18155, d181811, d184006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18155, d181811, d184006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18156 q = 1) (hb : d181811 q = 1) : d184007 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18156, d184007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18156, d184007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d17027 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10115 q = 1) (hb : d102052 q = 1) : d10115 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d17028 q = 1) (hb : d181810 q = 1) : d10116 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17028, d181810, d10116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d17028, d181810, d10116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18157 q = 1) (hb : d181811 q = 1) : d184008 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18157, d181811, d184008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18157, d181811, d184008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d18158 q = 1) (hb : d181811 q = 1) : d184009 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18158, d184009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18158, d184009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d18159 q = 1) (hb : d181811 q = 1) : d184010 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18159, d184010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18159, d184010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d15397 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d10085 q = 1) (hb : d102052 q = 1) : d10085 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d15398 q = 1) (hb : d181810 q = 1) : d10086 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15398, d181810, d10086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d15398, d181810, d10086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d18139 q = 1) (hb : d181811 q = 1) : d183990 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18139, d181811, d183990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18139, d181811, d183990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h17 (q : Pattern) (ha : d18140 q = 1) (hb : d181811 q = 1) : d183991 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18140, d183991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d18140, d183991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d18149 q = 1) (hb : d181811 q = 1) : d184000 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18149, d184000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d18149, d184000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h19 (q : Pattern) (ha : d18160 q = 1) (hb : d181811 q = 1) : d184011 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18160, d184011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18160, d184011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro41212 (p : Pattern) (ha : d18191 p = 1) (hb : d181811 p = 1) : d184042 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1868 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1582 q = 1) (hb : d102052 q = 1) : d1582 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1869 q = 1) (hb : d181810 q = 1) : d10159 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, d181810, d10159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1869, d181810, d10159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18188 q = 1) (hb : d181811 q = 1) : d184039 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18188, d181811, d184039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18188, d181811, d184039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18189 q = 1) (hb : d181811 q = 1) : d184040 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18189, d184040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18189, d184040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18190 q = 1) (hb : d181811 q = 1) : d184041 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18190, d184041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18190, d184041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d15412 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d10135 q = 1) (hb : d102052 q = 1) : d10135 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15413 q = 1) (hb : d181810 q = 1) : d10136 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15413, d181810, d10136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d15413, d181810, d10136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18167 q = 1) (hb : d181811 q = 1) : d184018 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18167, d181811, d184018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18167, d181811, d184018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d18168 q = 1) (hb : d181811 q = 1) : d184019 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18168, d184019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18168, d184019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h13 (q : Pattern) (ha : d18169 q = 1) (hb : d181811 q = 1) : d184020 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18169, d184020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18169, d184020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d18191 q = 1) (hb : d181811 q = 1) : d184042 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18191, d184042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18191, d184042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro41213 (p : Pattern) (ha : d18197 p = 1) (hb : d181811 p = 1) : d184048 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18192 q = 1) (hb : d181811 q = 1) : d184043 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18192, d184043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41211 q ha hb
    | true =>
      simp only [d18192, d184043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41212 q ha hb
  have h2 (q : Pattern) (ha : d18193 q = 1) (hb : d181811 q = 1) : d184044 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18193, d184044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18193, d184044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18194 q = 1) (hb : d181811 q = 1) : d184045 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18194, d184045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18194, d184045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18195 q = 1) (hb : d181811 q = 1) : d184046 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18195, d184046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18195, d184046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18196 q = 1) (hb : d181811 q = 1) : d184047 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18196, d184047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18196, d184047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18197 q = 1) (hb : d181811 q = 1) : d184048 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18197, d184048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18197, d184048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41214 (p : Pattern) (ha : d18286 p = 1) (hb : d181811 p = 1) : d184080 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18198 q = 1) (hb : d181811 q = 1) : d184049 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18198, d184049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41213 q ha hb
    | true =>
      simp only [d18198, d184049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18199 q = 1) (hb : d181811 q = 1) : d184050 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18199, d184050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18199, d184050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18283 q = 1) (hb : d181811 q = 1) : d184077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18283, d184077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18283, d184077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18284 q = 1) (hb : d181811 q = 1) : d184078 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18284, d184078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18284, d184078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18285 q = 1) (hb : d181811 q = 1) : d184079 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18285, d184079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18285, d184079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18286 q = 1) (hb : d181811 q = 1) : d184080 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18286, d184080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18286, d184080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41215 (p : Pattern) (ha : d18292 p = 1) (hb : d181811 p = 1) : d184086 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18287 q = 1) (hb : d181811 q = 1) : d184081 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18287, d184081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41214 q ha hb
    | true =>
      simp only [d18287, d184081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18288 q = 1) (hb : d181811 q = 1) : d184082 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18288, d184082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18288, d184082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18289 q = 1) (hb : d181811 q = 1) : d184083 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18289, d184083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18289, d184083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18290 q = 1) (hb : d181811 q = 1) : d184084 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18290, d184084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18290, d184084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18291 q = 1) (hb : d181811 q = 1) : d184085 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18291, d184085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18291, d184085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18292 q = 1) (hb : d181811 q = 1) : d184086 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18292, d184086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18292, d184086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41216 (p : Pattern) (ha : d18133 p = 1) (hb : d181811 p = 1) : d183984 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1853 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1665 q = 1) (hb : d102052 q = 1) : d1665 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1854 q = 1) (hb : d181810 q = 1) : d10032 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1854, d181810, d10032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1854, d181810, d10032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18123 q = 1) (hb : d181811 q = 1) : d183974 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18123, d181811, d183974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18123, d181811, d183974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18124 q = 1) (hb : d181811 q = 1) : d183975 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18124, d183975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18124, d183975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d17004 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10036 q = 1) (hb : d102052 q = 1) : d10036 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d17005 q = 1) (hb : d181810 q = 1) : d10037 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17005, d181810, d10037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d17005, d181810, d10037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18125 q = 1) (hb : d181811 q = 1) : d183976 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18125, d181811, d183976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18125, d181811, d183976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d18126 q = 1) (hb : d181811 q = 1) : d183977 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18126, d183977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18126, d183977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d18127 q = 1) (hb : d181811 q = 1) : d183978 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18127, d183978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18127, d183978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d15380 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d10046 q = 1) (hb : d102052 q = 1) : d10046 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d15381 q = 1) (hb : d181810 q = 1) : d10047 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15381, d181810, d10047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d15381, d181810, d10047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d18128 q = 1) (hb : d181811 q = 1) : d183979 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18128, d181811, d183979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18128, d181811, d183979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h17 (q : Pattern) (ha : d18129 q = 1) (hb : d181811 q = 1) : d183980 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18129, d183980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d18129, d183980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d15387 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d10063 q = 1) (hb : d102052 q = 1) : d10063 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d15388 q = 1) (hb : d181810 q = 1) : d10064 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15388, d181810, d10064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d15388, d181810, d10064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d18130 q = 1) (hb : d181811 q = 1) : d183981 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18130, d181811, d183981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d18130, d181811, d183981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h22 (q : Pattern) (ha : d18131 q = 1) (hb : d181811 q = 1) : d183982 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18131, d183982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d18131, d183982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h23 (q : Pattern) (ha : d18132 q = 1) (hb : d181811 q = 1) : d183983 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18132, d183983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d18132, d183983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d18133 q = 1) (hb : d181811 q = 1) : d183984 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18133, d183984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18133, d183984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro41217 (p : Pattern) (ha : d18142 p = 1) (hb : d181811 p = 1) : d183993 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1857 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1555 q = 1) (hb : d102052 q = 1) : d1555 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1858 q = 1) (hb : d181810 q = 1) : d10070 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1858, d181810, d10070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1858, d181810, d10070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18134 q = 1) (hb : d181811 q = 1) : d183985 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18134, d181811, d183985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18134, d181811, d183985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18135 q = 1) (hb : d181811 q = 1) : d183986 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18135, d183986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18135, d183986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d17011 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10074 q = 1) (hb : d102052 q = 1) : d10074 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d17012 q = 1) (hb : d181810 q = 1) : d10075 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17012, d181810, d10075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d17012, d181810, d10075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18136 q = 1) (hb : d181811 q = 1) : d183987 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18136, d181811, d183987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18136, d181811, d183987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d18137 q = 1) (hb : d181811 q = 1) : d183988 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18137, d183988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18137, d183988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d18138 q = 1) (hb : d181811 q = 1) : d183989 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18138, d183989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18138, d183989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d15387 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d10063 q = 1) (hb : d102052 q = 1) : d10063 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d15388 q = 1) (hb : d181810 q = 1) : d10064 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15388, d181810, d10064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d15388, d181810, d10064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d18130 q = 1) (hb : d181811 q = 1) : d183981 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18130, d181811, d183981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18130, d181811, d183981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h17 (q : Pattern) (ha : d18131 q = 1) (hb : d181811 q = 1) : d183982 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18131, d183982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d18131, d183982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d15397 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d10085 q = 1) (hb : d102052 q = 1) : d10085 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d15398 q = 1) (hb : d181810 q = 1) : d10086 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15398, d181810, d10086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d15398, d181810, d10086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d18139 q = 1) (hb : d181811 q = 1) : d183990 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18139, d181811, d183990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d18139, d181811, d183990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h22 (q : Pattern) (ha : d18140 q = 1) (hb : d181811 q = 1) : d183991 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18140, d183991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d18140, d183991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h23 (q : Pattern) (ha : d18141 q = 1) (hb : d181811 q = 1) : d183992 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18141, d183992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d18141, d183992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d18142 q = 1) (hb : d181811 q = 1) : d183993 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18142, d183993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18142, d183993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro41218 (p : Pattern) (ha : d18150 p = 1) (hb : d181811 p = 1) : d184001 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10099 q = 1) (hb : d102052 q = 1) : d10099 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13487 q = 1) (hb : d181810 q = 1) : d10100 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13487, d181810, d10100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13487, d181810, d10100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18146 q = 1) (hb : d181811 q = 1) : d183997 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18146, d181811, d183997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18146, d181811, d183997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18147 q = 1) (hb : d181811 q = 1) : d183998 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18147, d183998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18147, d183998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d15397 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10085 q = 1) (hb : d102052 q = 1) : d10085 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15398 q = 1) (hb : d181810 q = 1) : d10086 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15398, d181810, d10086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d15398, d181810, d10086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18139 q = 1) (hb : d181811 q = 1) : d183990 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18139, d181811, d183990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18139, d181811, d183990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d18140 q = 1) (hb : d181811 q = 1) : d183991 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18140, d183991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18140, d183991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d18148 q = 1) (hb : d181811 q = 1) : d183999 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18148, d183999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18148, d183999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18149 q = 1) (hb : d181811 q = 1) : d184000 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18149, d184000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18149, d184000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d18150 q = 1) (hb : d181811 q = 1) : d184001 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18150, d184001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18150, d184001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro41219 (p : Pattern) (ha : d18170 p = 1) (hb : d181811 p = 1) : d184021 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6496 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5134 q = 1) (hb : d102052 q = 1) : d5134 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6497 q = 1) (hb : d181810 q = 1) : d10125 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6497, d181810, d10125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6497, d181810, d10125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18164 q = 1) (hb : d181811 q = 1) : d184015 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18164, d181811, d184015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18164, d181811, d184015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18165 q = 1) (hb : d181811 q = 1) : d184016 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18165, d184016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18165, d184016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18166 q = 1) (hb : d181811 q = 1) : d184017 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18166, d184017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18166, d184017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d15412 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d10135 q = 1) (hb : d102052 q = 1) : d10135 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15413 q = 1) (hb : d181810 q = 1) : d10136 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15413, d181810, d10136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d15413, d181810, d10136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18167 q = 1) (hb : d181811 q = 1) : d184018 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18167, d181811, d184018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18167, d181811, d184018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d18168 q = 1) (hb : d181811 q = 1) : d184019 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18168, d184019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18168, d184019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h13 (q : Pattern) (ha : d18169 q = 1) (hb : d181811 q = 1) : d184020 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18169, d184020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18169, d184020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d18170 q = 1) (hb : d181811 q = 1) : d184021 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18170, d184021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18170, d184021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro41220 (p : Pattern) (ha : d18176 p = 1) (hb : d181811 p = 1) : d184027 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18143 q = 1) (hb : d181811 q = 1) : d183994 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18143, d183994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41216 q ha hb
    | true =>
      simp only [d18143, d183994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41217 q ha hb
  have h2 (q : Pattern) (ha : d18144 q = 1) (hb : d181811 q = 1) : d183995 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18144, d183995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18144, d183995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18145 q = 1) (hb : d181811 q = 1) : d183996 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18145, d183996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18145, d183996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18151 q = 1) (hb : d181811 q = 1) : d184002 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18151, d184002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41217 q ha hb
    | true =>
      simp only [d18151, d184002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41218 q ha hb
  have h5 (q : Pattern) (ha : d18152 q = 1) (hb : d181811 q = 1) : d184003 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18152, d184003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18152, d184003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18153 q = 1) (hb : d181811 q = 1) : d184004 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18153, d184004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18153, d184004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18154 q = 1) (hb : d181811 q = 1) : d184005 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18154, d184005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18154, d184005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18161 q = 1) (hb : d181811 q = 1) : d184012 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18161, d184012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41217 q ha hb
    | true =>
      simp only [d18161, d184012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41211 q ha hb
  have h9 (q : Pattern) (ha : d18162 q = 1) (hb : d181811 q = 1) : d184013 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18162, d184013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18162, d184013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18163 q = 1) (hb : d181811 q = 1) : d184014 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18163, d184014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18163, d184014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18171 q = 1) (hb : d181811 q = 1) : d184022 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18171, d184022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41211 q ha hb
    | true =>
      simp only [d18171, d184022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41219 q ha hb
  have h12 (q : Pattern) (ha : d18172 q = 1) (hb : d181811 q = 1) : d184023 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18172, d184023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18172, d184023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18173 q = 1) (hb : d181811 q = 1) : d184024 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18173, d184024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18173, d184024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d18174 q = 1) (hb : d181811 q = 1) : d184025 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18174, d184025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18174, d184025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d18175 q = 1) (hb : d181811 q = 1) : d184026 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18175, d184026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18175, d184026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d18176 q = 1) (hb : d181811 q = 1) : d184027 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18176, d184027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18176, d184027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro41221 (p : Pattern) (ha : d18181 p = 1) (hb : d181811 p = 1) : d184032 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18161 q = 1) (hb : d181811 q = 1) : d184012 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18161, d184012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41217 q ha hb
    | true =>
      simp only [d18161, d184012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41211 q ha hb
  have h2 (q : Pattern) (ha : d18162 q = 1) (hb : d181811 q = 1) : d184013 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18162, d184013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18162, d184013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18163 q = 1) (hb : d181811 q = 1) : d184014 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18163, d184014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18163, d184014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18171 q = 1) (hb : d181811 q = 1) : d184022 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18171, d184022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41211 q ha hb
    | true =>
      simp only [d18171, d184022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41219 q ha hb
  have h5 (q : Pattern) (ha : d18172 q = 1) (hb : d181811 q = 1) : d184023 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18172, d184023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18172, d184023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18173 q = 1) (hb : d181811 q = 1) : d184024 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18173, d184024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18173, d184024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18174 q = 1) (hb : d181811 q = 1) : d184025 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18174, d184025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18174, d184025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18179 q = 1) (hb : d181811 q = 1) : d184030 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18179, d184030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18179, d184030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d18180 q = 1) (hb : d181811 q = 1) : d184031 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18180, d184031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18180, d184031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18181 q = 1) (hb : d181811 q = 1) : d184032 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18181, d184032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18181, d184032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro41222 (p : Pattern) (ha : d18187 p = 1) (hb : d181811 p = 1) : d184038 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18177 q = 1) (hb : d181811 q = 1) : d184028 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18177, d184028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41220 q ha hb
    | true =>
      simp only [d18177, d184028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18178 q = 1) (hb : d181811 q = 1) : d184029 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18178, d184029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18178, d184029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18182 q = 1) (hb : d181811 q = 1) : d184033 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18182, d184033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41221 q ha hb
    | true =>
      simp only [d18182, d184033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18183 q = 1) (hb : d181811 q = 1) : d184034 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18183, d184034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18183, d184034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18184 q = 1) (hb : d181811 q = 1) : d184035 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18184, d184035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18184, d184035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18185 q = 1) (hb : d181811 q = 1) : d184036 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18185, d184036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18185, d184036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18186 q = 1) (hb : d181811 q = 1) : d184037 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18186, d184037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18186, d184037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18187 q = 1) (hb : d181811 q = 1) : d184038 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18187, d184038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18187, d184038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41223 (p : Pattern) (ha : d18203 p = 1) (hb : d181811 p = 1) : d184054 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18182 q = 1) (hb : d181811 q = 1) : d184033 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18182, d184033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41221 q ha hb
    | true =>
      simp only [d18182, d184033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18183 q = 1) (hb : d181811 q = 1) : d184034 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18183, d184034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18183, d184034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18198 q = 1) (hb : d181811 q = 1) : d184049 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18198, d184049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41213 q ha hb
    | true =>
      simp only [d18198, d184049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18199 q = 1) (hb : d181811 q = 1) : d184050 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18199, d184050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18199, d184050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18200 q = 1) (hb : d181811 q = 1) : d184051 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18200, d184051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18200, d184051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18201 q = 1) (hb : d181811 q = 1) : d184052 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18201, d184052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18201, d184052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18202 q = 1) (hb : d181811 q = 1) : d184053 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18202, d184053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18202, d184053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18203 q = 1) (hb : d181811 q = 1) : d184054 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18203, d184054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18203, d184054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41224 (p : Pattern) (ha : d18263 p = 1) (hb : d181811 p = 1) : d184057 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1868 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1582 q = 1) (hb : d102052 q = 1) : d1582 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1869 q = 1) (hb : d181810 q = 1) : d10159 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, d181810, d10159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1869, d181810, d10159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18188 q = 1) (hb : d181811 q = 1) : d184039 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18188, d181811, d184039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18188, d181811, d184039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18189 q = 1) (hb : d181811 q = 1) : d184040 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18189, d184040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18189, d184040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18190 q = 1) (hb : d181811 q = 1) : d184041 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18190, d184041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18190, d184041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d18263 q = 1) (hb : d181811 q = 1) : d184057 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18263, d184057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18263, d184057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro41225 (p : Pattern) (ha : d18269 p = 1) (hb : d181811 p = 1) : d184063 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18161 q = 1) (hb : d181811 q = 1) : d184012 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18161, d184012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41217 q ha hb
    | true =>
      simp only [d18161, d184012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41211 q ha hb
  have h2 (q : Pattern) (ha : d18162 q = 1) (hb : d181811 q = 1) : d184013 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18162, d184013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18162, d184013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18163 q = 1) (hb : d181811 q = 1) : d184014 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18163, d184014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18163, d184014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18171 q = 1) (hb : d181811 q = 1) : d184022 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18171, d184022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41211 q ha hb
    | true =>
      simp only [d18171, d184022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41219 q ha hb
  have h5 (q : Pattern) (ha : d18172 q = 1) (hb : d181811 q = 1) : d184023 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18172, d184023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18172, d184023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18173 q = 1) (hb : d181811 q = 1) : d184024 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18173, d184024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18173, d184024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18174 q = 1) (hb : d181811 q = 1) : d184025 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18174, d184025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18174, d184025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18264 q = 1) (hb : d181811 q = 1) : d184058 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18264, d184058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41211 q ha hb
    | true =>
      simp only [d18264, d184058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41224 q ha hb
  have h9 (q : Pattern) (ha : d18265 q = 1) (hb : d181811 q = 1) : d184059 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18265, d184059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18265, d184059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18266 q = 1) (hb : d181811 q = 1) : d184060 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18266, d184060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18266, d184060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18267 q = 1) (hb : d181811 q = 1) : d184061 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18267, d184061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18267, d184061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d18268 q = 1) (hb : d181811 q = 1) : d184062 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18268, d184062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18268, d184062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18269 q = 1) (hb : d181811 q = 1) : d184063 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18269, d184063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18269, d184063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro41226 (p : Pattern) (ha : d18275 p = 1) (hb : d181811 p = 1) : d184069 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18270 q = 1) (hb : d181811 q = 1) : d184064 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18270, d184064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41225 q ha hb
    | true =>
      simp only [d18270, d184064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18271 q = 1) (hb : d181811 q = 1) : d184065 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18271, d184065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18271, d184065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18272 q = 1) (hb : d181811 q = 1) : d184066 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18272, d184066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18272, d184066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18273 q = 1) (hb : d181811 q = 1) : d184067 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18273, d184067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18273, d184067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18274 q = 1) (hb : d181811 q = 1) : d184068 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18274, d184068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18274, d184068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18275 q = 1) (hb : d181811 q = 1) : d184069 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18275, d184069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18275, d184069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41227 (p : Pattern) (ha : d129389 p = 1) (hb : d181811 p = 1) : d184075 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18204 q = 1) (hb : d181811 q = 1) : d184055 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18204, d184055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41222 q ha hb
    | true =>
      simp only [d18204, d184055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41223 q ha hb
  have h2 (q : Pattern) (ha : d129385 q = 1) (hb : d181811 q = 1) : d184056 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129385, d184056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129385, d184056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d18276 q = 1) (hb : d181811 q = 1) : d184070 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18276, d184070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41226 q ha hb
    | true =>
      simp only [d18276, d184070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18277 q = 1) (hb : d181811 q = 1) : d184071 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18277, d184071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18277, d184071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129386 q = 1) (hb : d181811 q = 1) : d184072 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129386, d184072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129386, d184072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129387 q = 1) (hb : d181811 q = 1) : d184073 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129387, d184073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129387, d184073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129388 q = 1) (hb : d181811 q = 1) : d184074 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129388, d184074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129388, d184074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129389 q = 1) (hb : d181811 q = 1) : d184075 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129389, d184075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129389, d184075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41228 (p : Pattern) (ha : d129395 p = 1) (hb : d181811 p = 1) : d184092 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129390 q = 1) (hb : d181811 q = 1) : d184076 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129390, d184076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129390, d184076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41227 q ha hb
  have h2 (q : Pattern) (ha : d18293 q = 1) (hb : d181811 q = 1) : d184087 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18293, d184087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18293, d184087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41215 q ha hb
  have h3 (q : Pattern) (ha : d129391 q = 1) (hb : d181811 q = 1) : d184088 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129391, d184088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129391, d184088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129392 q = 1) (hb : d181811 q = 1) : d184089 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129392, d184089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129392, d184089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129393 q = 1) (hb : d181811 q = 1) : d184090 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129393, d184090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129393, d184090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129394 q = 1) (hb : d181811 q = 1) : d184091 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129394, d184091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129394, d184091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129395 q = 1) (hb : d181811 q = 1) : d184092 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129395, d184092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129395, d184092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41229 (p : Pattern) (ha : d129401 p = 1) (hb : d181811 p = 1) : d184098 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129396 q = 1) (hb : d181811 q = 1) : d184093 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129396, d184093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129396, d184093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41228 q ha hb
  have h2 (q : Pattern) (ha : d129397 q = 1) (hb : d181811 q = 1) : d184094 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129397, d184094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129397, d184094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129398 q = 1) (hb : d181811 q = 1) : d184095 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129398, d184095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129398, d184095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129399 q = 1) (hb : d181811 q = 1) : d184096 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129399, d184096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129399, d184096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129400 q = 1) (hb : d181811 q = 1) : d184097 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129400, d184097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129400, d184097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129401 q = 1) (hb : d181811 q = 1) : d184098 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129401, d184098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129401, d184098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41230 (p : Pattern) (ha : d18341 p = 1) (hb : d181811 p = 1) : d184135 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2340 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2053 q = 1) (hb : d102052 q = 1) : d2053 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2341 q = 1) (hb : d181810 q = 1) : d10387 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2341, d181810, d10387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2341, d181810, d10387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18336 q = 1) (hb : d181811 q = 1) : d184130 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18336, d181811, d184130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18336, d181811, d184130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18337 q = 1) (hb : d181811 q = 1) : d184131 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18337, d184131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18337, d184131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d17391 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10391 q = 1) (hb : d102052 q = 1) : d10391 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d17392 q = 1) (hb : d181810 q = 1) : d10392 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17392, d181810, d10392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d17392, d181810, d10392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18338 q = 1) (hb : d181811 q = 1) : d184132 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18338, d181811, d184132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18338, d181811, d184132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d18339 q = 1) (hb : d181811 q = 1) : d184133 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18339, d184133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18339, d184133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d18340 q = 1) (hb : d181811 q = 1) : d184134 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18340, d184134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18340, d184134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d15775 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d10371 q = 1) (hb : d102052 q = 1) : d10371 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d15776 q = 1) (hb : d181810 q = 1) : d10372 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15776, d181810, d10372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d15776, d181810, d10372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d18323 q = 1) (hb : d181811 q = 1) : d184117 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18323, d181811, d184117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18323, d181811, d184117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h17 (q : Pattern) (ha : d18324 q = 1) (hb : d181811 q = 1) : d184118 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18324, d184118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d18324, d184118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d18330 q = 1) (hb : d181811 q = 1) : d184124 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18330, d184124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d18330, d184124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h19 (q : Pattern) (ha : d18341 q = 1) (hb : d181811 q = 1) : d184135 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18341, d184135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18341, d184135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro41231 (p : Pattern) (ha : d18372 p = 1) (hb : d181811 p = 1) : d184166 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2346 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2065 q = 1) (hb : d102052 q = 1) : d2065 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2347 q = 1) (hb : d181810 q = 1) : d10436 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2347, d181810, d10436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2347, d181810, d10436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18369 q = 1) (hb : d181811 q = 1) : d184163 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18369, d181811, d184163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18369, d181811, d184163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18370 q = 1) (hb : d181811 q = 1) : d184164 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18370, d184164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18370, d184164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18371 q = 1) (hb : d181811 q = 1) : d184165 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18371, d184165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18371, d184165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d15790 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d10412 q = 1) (hb : d102052 q = 1) : d10412 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15791 q = 1) (hb : d181810 q = 1) : d10413 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15791, d181810, d10413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d15791, d181810, d10413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18348 q = 1) (hb : d181811 q = 1) : d184142 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18348, d181811, d184142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18348, d181811, d184142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d18349 q = 1) (hb : d181811 q = 1) : d184143 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18349, d184143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18349, d184143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h13 (q : Pattern) (ha : d18350 q = 1) (hb : d181811 q = 1) : d184144 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18350, d184144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18350, d184144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d18372 q = 1) (hb : d181811 q = 1) : d184166 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18372, d184166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18372, d184166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro41232 (p : Pattern) (ha : d18378 p = 1) (hb : d181811 p = 1) : d184172 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18373 q = 1) (hb : d181811 q = 1) : d184167 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18373, d184167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41230 q ha hb
    | true =>
      simp only [d18373, d184167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41231 q ha hb
  have h2 (q : Pattern) (ha : d18374 q = 1) (hb : d181811 q = 1) : d184168 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18374, d184168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18374, d184168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18375 q = 1) (hb : d181811 q = 1) : d184169 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18375, d184169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18375, d184169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18376 q = 1) (hb : d181811 q = 1) : d184170 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18376, d184170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18376, d184170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18377 q = 1) (hb : d181811 q = 1) : d184171 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18377, d184171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18377, d184171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18378 q = 1) (hb : d181811 q = 1) : d184172 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18378, d184172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18378, d184172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41233 (p : Pattern) (ha : d18467 p = 1) (hb : d181811 p = 1) : d184204 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18379 q = 1) (hb : d181811 q = 1) : d184173 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18379, d184173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41232 q ha hb
    | true =>
      simp only [d18379, d184173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18380 q = 1) (hb : d181811 q = 1) : d184174 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18380, d184174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18380, d184174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18464 q = 1) (hb : d181811 q = 1) : d184201 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18464, d184201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18464, d184201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18465 q = 1) (hb : d181811 q = 1) : d184202 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18465, d184202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18465, d184202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18466 q = 1) (hb : d181811 q = 1) : d184203 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18466, d184203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18466, d184203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18467 q = 1) (hb : d181811 q = 1) : d184204 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18467, d184204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18467, d184204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41234 (p : Pattern) (ha : d18473 p = 1) (hb : d181811 p = 1) : d184210 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18468 q = 1) (hb : d181811 q = 1) : d184205 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18468, d184205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41233 q ha hb
    | true =>
      simp only [d18468, d184205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18469 q = 1) (hb : d181811 q = 1) : d184206 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18469, d184206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18469, d184206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18470 q = 1) (hb : d181811 q = 1) : d184207 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18470, d184207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18470, d184207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18471 q = 1) (hb : d181811 q = 1) : d184208 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18471, d184208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18471, d184208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18472 q = 1) (hb : d181811 q = 1) : d184209 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18472, d184209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18472, d184209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18473 q = 1) (hb : d181811 q = 1) : d184210 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18473, d184210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18473, d184210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41235 (p : Pattern) (ha : d18317 p = 1) (hb : d181811 p = 1) : d184111 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2331 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2144 q = 1) (hb : d102052 q = 1) : d2144 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2332 q = 1) (hb : d181810 q = 1) : d10339 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2332, d181810, d10339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2332, d181810, d10339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18309 q = 1) (hb : d181811 q = 1) : d184103 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18309, d181811, d184103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18309, d181811, d184103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18310 q = 1) (hb : d181811 q = 1) : d184104 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18310, d184104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18310, d184104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d17369 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10343 q = 1) (hb : d102052 q = 1) : d10343 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d17370 q = 1) (hb : d181810 q = 1) : d10344 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17370, d181810, d10344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d17370, d181810, d10344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18311 q = 1) (hb : d181811 q = 1) : d184105 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18311, d181811, d184105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18311, d181811, d184105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d18312 q = 1) (hb : d181811 q = 1) : d184106 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18312, d184106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18312, d184106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d18313 q = 1) (hb : d181811 q = 1) : d184107 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18313, d184107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18313, d184107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d13813 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d10353 q = 1) (hb : d102052 q = 1) : d10353 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d13814 q = 1) (hb : d181810 q = 1) : d10354 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d181810, d10354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d13814, d181810, d10354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d18314 q = 1) (hb : d181811 q = 1) : d184108 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18314, d181811, d184108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18314, d181811, d184108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h17 (q : Pattern) (ha : d18315 q = 1) (hb : d181811 q = 1) : d184109 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18315, d184109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d18315, d184109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d18316 q = 1) (hb : d181811 q = 1) : d184110 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18316, d184110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18316, d184110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d18317 q = 1) (hb : d181811 q = 1) : d184111 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18317, d184111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18317, d184111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro41236 (p : Pattern) (ha : d18326 p = 1) (hb : d181811 p = 1) : d184120 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2035 q = 1) (hb : d102052 q = 1) : d2035 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2336 q = 1) (hb : d181810 q = 1) : d10360 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2336, d181810, d10360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2336, d181810, d10360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18318 q = 1) (hb : d181811 q = 1) : d184112 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18318, d181811, d184112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18318, d181811, d184112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18319 q = 1) (hb : d181811 q = 1) : d184113 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18319, d184113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18319, d184113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d17376 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10364 q = 1) (hb : d102052 q = 1) : d10364 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d17377 q = 1) (hb : d181810 q = 1) : d10365 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17377, d181810, d10365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d17377, d181810, d10365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18320 q = 1) (hb : d181811 q = 1) : d184114 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18320, d181811, d184114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18320, d181811, d184114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d18321 q = 1) (hb : d181811 q = 1) : d184115 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18321, d184115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18321, d184115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d18322 q = 1) (hb : d181811 q = 1) : d184116 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18322, d184116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18322, d184116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d13813 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d10353 q = 1) (hb : d102052 q = 1) : d10353 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d13814 q = 1) (hb : d181810 q = 1) : d10354 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d181810, d10354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d13814, d181810, d10354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d18314 q = 1) (hb : d181811 q = 1) : d184108 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18314, d181811, d184108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18314, d181811, d184108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h17 (q : Pattern) (ha : d18315 q = 1) (hb : d181811 q = 1) : d184109 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18315, d184109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d18315, d184109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d15775 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d10371 q = 1) (hb : d102052 q = 1) : d10371 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d15776 q = 1) (hb : d181810 q = 1) : d10372 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15776, d181810, d10372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d15776, d181810, d10372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d18323 q = 1) (hb : d181811 q = 1) : d184117 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18323, d181811, d184117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d18323, d181811, d184117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h22 (q : Pattern) (ha : d18324 q = 1) (hb : d181811 q = 1) : d184118 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18324, d184118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d18324, d184118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h23 (q : Pattern) (ha : d18325 q = 1) (hb : d181811 q = 1) : d184119 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18325, d184119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d18325, d184119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d18326 q = 1) (hb : d181811 q = 1) : d184120 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18326, d184120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18326, d184120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro41237 (p : Pattern) (ha : d18331 p = 1) (hb : d181811 p = 1) : d184125 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13813 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10353 q = 1) (hb : d102052 q = 1) : d10353 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13814 q = 1) (hb : d181810 q = 1) : d10354 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d181810, d10354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13814, d181810, d10354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18314 q = 1) (hb : d181811 q = 1) : d184108 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18314, d181811, d184108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18314, d181811, d184108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18315 q = 1) (hb : d181811 q = 1) : d184109 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18315, d184109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18315, d184109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d15775 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10371 q = 1) (hb : d102052 q = 1) : d10371 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15776 q = 1) (hb : d181810 q = 1) : d10372 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15776, d181810, d10372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d15776, d181810, d10372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18323 q = 1) (hb : d181811 q = 1) : d184117 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18323, d181811, d184117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18323, d181811, d184117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d18324 q = 1) (hb : d181811 q = 1) : d184118 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18324, d184118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18324, d184118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d18325 q = 1) (hb : d181811 q = 1) : d184119 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18325, d184119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18325, d184119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18330 q = 1) (hb : d181811 q = 1) : d184124 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18330, d184124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18330, d184124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d18331 q = 1) (hb : d181811 q = 1) : d184125 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18331, d184125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18331, d184125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro41238 (p : Pattern) (ha : d18351 p = 1) (hb : d181811 p = 1) : d184145 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6643 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5247 q = 1) (hb : d102052 q = 1) : d5247 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6644 q = 1) (hb : d181810 q = 1) : d10401 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6644, d181810, d10401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6644, d181810, d10401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18345 q = 1) (hb : d181811 q = 1) : d184139 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18345, d181811, d184139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18345, d181811, d184139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18346 q = 1) (hb : d181811 q = 1) : d184140 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18346, d184140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18346, d184140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18347 q = 1) (hb : d181811 q = 1) : d184141 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18347, d184141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18347, d184141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d15790 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d10412 q = 1) (hb : d102052 q = 1) : d10412 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15791 q = 1) (hb : d181810 q = 1) : d10413 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15791, d181810, d10413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d15791, d181810, d10413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18348 q = 1) (hb : d181811 q = 1) : d184142 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18348, d181811, d184142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18348, d181811, d184142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d18349 q = 1) (hb : d181811 q = 1) : d184143 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18349, d184143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18349, d184143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h13 (q : Pattern) (ha : d18350 q = 1) (hb : d181811 q = 1) : d184144 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18350, d184144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18350, d184144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h14 (q : Pattern) (ha : d18351 q = 1) (hb : d181811 q = 1) : d184145 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18351, d184145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18351, d184145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro41239 (p : Pattern) (ha : d18357 p = 1) (hb : d181811 p = 1) : d184151 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18327 q = 1) (hb : d181811 q = 1) : d184121 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18327, d184121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41235 q ha hb
    | true =>
      simp only [d18327, d184121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41236 q ha hb
  have h2 (q : Pattern) (ha : d18328 q = 1) (hb : d181811 q = 1) : d184122 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18328, d184122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18328, d184122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18329 q = 1) (hb : d181811 q = 1) : d184123 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18329, d184123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18329, d184123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18332 q = 1) (hb : d181811 q = 1) : d184126 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18332, d184126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41236 q ha hb
    | true =>
      simp only [d18332, d184126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41237 q ha hb
  have h5 (q : Pattern) (ha : d18333 q = 1) (hb : d181811 q = 1) : d184127 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18333, d184127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18333, d184127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18334 q = 1) (hb : d181811 q = 1) : d184128 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18334, d184128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18334, d184128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18335 q = 1) (hb : d181811 q = 1) : d184129 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18335, d184129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18335, d184129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18342 q = 1) (hb : d181811 q = 1) : d184136 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18342, d184136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41236 q ha hb
    | true =>
      simp only [d18342, d184136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41230 q ha hb
  have h9 (q : Pattern) (ha : d18343 q = 1) (hb : d181811 q = 1) : d184137 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18343, d184137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18343, d184137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18344 q = 1) (hb : d181811 q = 1) : d184138 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18344, d184138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18344, d184138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18352 q = 1) (hb : d181811 q = 1) : d184146 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18352, d184146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41230 q ha hb
    | true =>
      simp only [d18352, d184146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41238 q ha hb
  have h12 (q : Pattern) (ha : d18353 q = 1) (hb : d181811 q = 1) : d184147 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18353, d184147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18353, d184147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18354 q = 1) (hb : d181811 q = 1) : d184148 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18354, d184148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18354, d184148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d18355 q = 1) (hb : d181811 q = 1) : d184149 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18355, d184149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18355, d184149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d18356 q = 1) (hb : d181811 q = 1) : d184150 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18356, d184150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18356, d184150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d18357 q = 1) (hb : d181811 q = 1) : d184151 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18357, d184151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18357, d184151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro41240 (p : Pattern) (ha : d18362 p = 1) (hb : d181811 p = 1) : d184156 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18342 q = 1) (hb : d181811 q = 1) : d184136 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18342, d184136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41236 q ha hb
    | true =>
      simp only [d18342, d184136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41230 q ha hb
  have h2 (q : Pattern) (ha : d18343 q = 1) (hb : d181811 q = 1) : d184137 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18343, d184137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18343, d184137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18344 q = 1) (hb : d181811 q = 1) : d184138 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18344, d184138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18344, d184138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18352 q = 1) (hb : d181811 q = 1) : d184146 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18352, d184146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41230 q ha hb
    | true =>
      simp only [d18352, d184146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41238 q ha hb
  have h5 (q : Pattern) (ha : d18353 q = 1) (hb : d181811 q = 1) : d184147 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18353, d184147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18353, d184147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18354 q = 1) (hb : d181811 q = 1) : d184148 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18354, d184148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18354, d184148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18355 q = 1) (hb : d181811 q = 1) : d184149 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18355, d184149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18355, d184149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18360 q = 1) (hb : d181811 q = 1) : d184154 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18360, d184154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18360, d184154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d18361 q = 1) (hb : d181811 q = 1) : d184155 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18361, d184155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18361, d184155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18362 q = 1) (hb : d181811 q = 1) : d184156 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18362, d184156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18362, d184156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro41241 (p : Pattern) (ha : d18368 p = 1) (hb : d181811 p = 1) : d184162 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18358 q = 1) (hb : d181811 q = 1) : d184152 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18358, d184152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41239 q ha hb
    | true =>
      simp only [d18358, d184152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18359 q = 1) (hb : d181811 q = 1) : d184153 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18359, d184153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18359, d184153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18363 q = 1) (hb : d181811 q = 1) : d184157 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18363, d184157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41240 q ha hb
    | true =>
      simp only [d18363, d184157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18364 q = 1) (hb : d181811 q = 1) : d184158 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18364, d184158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18364, d184158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18365 q = 1) (hb : d181811 q = 1) : d184159 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18365, d184159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18365, d184159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18366 q = 1) (hb : d181811 q = 1) : d184160 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18366, d184160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18366, d184160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18367 q = 1) (hb : d181811 q = 1) : d184161 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18367, d184161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18367, d184161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18368 q = 1) (hb : d181811 q = 1) : d184162 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18368, d184162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18368, d184162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41242 (p : Pattern) (ha : d18384 p = 1) (hb : d181811 p = 1) : d184178 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18363 q = 1) (hb : d181811 q = 1) : d184157 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18363, d184157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41240 q ha hb
    | true =>
      simp only [d18363, d184157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18364 q = 1) (hb : d181811 q = 1) : d184158 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18364, d184158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18364, d184158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18379 q = 1) (hb : d181811 q = 1) : d184173 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18379, d184173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41232 q ha hb
    | true =>
      simp only [d18379, d184173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18380 q = 1) (hb : d181811 q = 1) : d184174 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18380, d184174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18380, d184174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18381 q = 1) (hb : d181811 q = 1) : d184175 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18381, d184175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18381, d184175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18382 q = 1) (hb : d181811 q = 1) : d184176 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18382, d184176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18382, d184176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18383 q = 1) (hb : d181811 q = 1) : d184177 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18383, d184177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18383, d184177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18384 q = 1) (hb : d181811 q = 1) : d184178 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18384, d184178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18384, d184178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41243 (p : Pattern) (ha : d18444 p = 1) (hb : d181811 p = 1) : d184181 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2346 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2065 q = 1) (hb : d102052 q = 1) : d2065 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2347 q = 1) (hb : d181810 q = 1) : d10436 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2347, d181810, d10436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2347, d181810, d10436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18369 q = 1) (hb : d181811 q = 1) : d184163 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18369, d181811, d184163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18369, d181811, d184163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18370 q = 1) (hb : d181811 q = 1) : d184164 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18370, d184164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18370, d184164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18371 q = 1) (hb : d181811 q = 1) : d184165 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18371, d184165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18371, d184165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d18444 q = 1) (hb : d181811 q = 1) : d184181 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18444, d184181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18444, d184181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro41244 (p : Pattern) (ha : d18450 p = 1) (hb : d181811 p = 1) : d184187 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18342 q = 1) (hb : d181811 q = 1) : d184136 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18342, d184136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41236 q ha hb
    | true =>
      simp only [d18342, d184136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41230 q ha hb
  have h2 (q : Pattern) (ha : d18343 q = 1) (hb : d181811 q = 1) : d184137 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18343, d184137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18343, d184137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18344 q = 1) (hb : d181811 q = 1) : d184138 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18344, d184138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18344, d184138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18352 q = 1) (hb : d181811 q = 1) : d184146 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18352, d184146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41230 q ha hb
    | true =>
      simp only [d18352, d184146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41238 q ha hb
  have h5 (q : Pattern) (ha : d18353 q = 1) (hb : d181811 q = 1) : d184147 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18353, d184147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18353, d184147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18354 q = 1) (hb : d181811 q = 1) : d184148 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18354, d184148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18354, d184148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18355 q = 1) (hb : d181811 q = 1) : d184149 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18355, d184149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18355, d184149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18445 q = 1) (hb : d181811 q = 1) : d184182 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18445, d184182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41230 q ha hb
    | true =>
      simp only [d18445, d184182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41243 q ha hb
  have h9 (q : Pattern) (ha : d18446 q = 1) (hb : d181811 q = 1) : d184183 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18446, d184183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18446, d184183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18447 q = 1) (hb : d181811 q = 1) : d184184 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18447, d184184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18447, d184184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18448 q = 1) (hb : d181811 q = 1) : d184185 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18448, d184185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18448, d184185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d18449 q = 1) (hb : d181811 q = 1) : d184186 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18449, d184186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18449, d184186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18450 q = 1) (hb : d181811 q = 1) : d184187 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18450, d184187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18450, d184187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro41245 (p : Pattern) (ha : d18456 p = 1) (hb : d181811 p = 1) : d184193 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18451 q = 1) (hb : d181811 q = 1) : d184188 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18451, d184188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41244 q ha hb
    | true =>
      simp only [d18451, d184188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18452 q = 1) (hb : d181811 q = 1) : d184189 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18452, d184189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18452, d184189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18453 q = 1) (hb : d181811 q = 1) : d184190 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18453, d184190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18453, d184190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18454 q = 1) (hb : d181811 q = 1) : d184191 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18454, d184191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18454, d184191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18455 q = 1) (hb : d181811 q = 1) : d184192 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18455, d184192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18455, d184192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18456 q = 1) (hb : d181811 q = 1) : d184193 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18456, d184193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18456, d184193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41246 (p : Pattern) (ha : d129410 p = 1) (hb : d181811 p = 1) : d184199 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18385 q = 1) (hb : d181811 q = 1) : d184179 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18385, d184179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41241 q ha hb
    | true =>
      simp only [d18385, d184179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41242 q ha hb
  have h2 (q : Pattern) (ha : d129406 q = 1) (hb : d181811 q = 1) : d184180 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129406, d184180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129406, d184180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d18457 q = 1) (hb : d181811 q = 1) : d184194 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18457, d184194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41245 q ha hb
    | true =>
      simp only [d18457, d184194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18458 q = 1) (hb : d181811 q = 1) : d184195 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18458, d184195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18458, d184195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129407 q = 1) (hb : d181811 q = 1) : d184196 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129407, d184196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129407, d184196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129408 q = 1) (hb : d181811 q = 1) : d184197 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129408, d184197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129408, d184197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129409 q = 1) (hb : d181811 q = 1) : d184198 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129409, d184198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129409, d184198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129410 q = 1) (hb : d181811 q = 1) : d184199 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129410, d184199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129410, d184199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41247 (p : Pattern) (ha : d129416 p = 1) (hb : d181811 p = 1) : d184216 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129411 q = 1) (hb : d181811 q = 1) : d184200 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129411, d184200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129411, d184200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41246 q ha hb
  have h2 (q : Pattern) (ha : d18474 q = 1) (hb : d181811 q = 1) : d184211 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18474, d184211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18474, d184211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41234 q ha hb
  have h3 (q : Pattern) (ha : d129412 q = 1) (hb : d181811 q = 1) : d184212 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129412, d184212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129412, d184212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129413 q = 1) (hb : d181811 q = 1) : d184213 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129413, d184213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129413, d184213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129414 q = 1) (hb : d181811 q = 1) : d184214 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129414, d184214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129414, d184214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129415 q = 1) (hb : d181811 q = 1) : d184215 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129415, d184215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129415, d184215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129416 q = 1) (hb : d181811 q = 1) : d184216 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129416, d184216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129416, d184216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41248 (p : Pattern) (ha : d129422 p = 1) (hb : d181811 p = 1) : d184222 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129417 q = 1) (hb : d181811 q = 1) : d184217 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129417, d184217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129417, d184217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41247 q ha hb
  have h2 (q : Pattern) (ha : d129418 q = 1) (hb : d181811 q = 1) : d184218 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129418, d184218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129418, d184218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129419 q = 1) (hb : d181811 q = 1) : d184219 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129419, d184219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129419, d184219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129420 q = 1) (hb : d181811 q = 1) : d184220 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129420, d184220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129420, d184220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129421 q = 1) (hb : d181811 q = 1) : d184221 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129421, d184221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129421, d184221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129422 q = 1) (hb : d181811 q = 1) : d184222 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129422, d184222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129422, d184222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41249 (p : Pattern) (ha : d129428 p = 1) (hb : d181811 p = 1) : d184228 p = 1 := by
  have h0 (q : Pattern) (ha : d129345 q = 1) (hb : d181811 q = 1) : d183757 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129345, d183757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41162 q ha hb
    | true =>
      simp only [d129345, d183757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41175 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d129363 q = 1) (hb : d181811 q = 1) : d183846 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129363, d183846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129363, d183846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41191 q ha hb
  have h3 (q : Pattern) (ha : d129364 q = 1) (hb : d181811 q = 1) : d183847 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129364, d183847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129364, d183847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129382 q = 1) (hb : d181811 q = 1) : d183971 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129382, d183971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129382, d183971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41210 q ha hb
  have h5 (q : Pattern) (ha : d129383 q = 1) (hb : d181811 q = 1) : d183972 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129383, d183972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129383, d183972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129384 q = 1) (hb : d181811 q = 1) : d183973 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129384, d183973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129384, d183973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129402 q = 1) (hb : d181811 q = 1) : d184099 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129402, d184099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129402, d184099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41229 q ha hb
  have h8 (q : Pattern) (ha : d129403 q = 1) (hb : d181811 q = 1) : d184100 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129403, d184100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129403, d184100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129404 q = 1) (hb : d181811 q = 1) : d184101 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129404, d184101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129404, d184101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129405 q = 1) (hb : d181811 q = 1) : d184102 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d129405, d184102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129405, d184102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d129423 q = 1) (hb : d181811 q = 1) : d184223 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129423, d184223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129423, d184223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41248 q ha hb
  have h12 (q : Pattern) (ha : d129424 q = 1) (hb : d181811 q = 1) : d184224 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129424, d184224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129424, d184224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d129425 q = 1) (hb : d181811 q = 1) : d184225 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129425, d184225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129425, d184225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d129426 q = 1) (hb : d181811 q = 1) : d184226 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d129426, d184226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129426, d184226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d129427 q = 1) (hb : d181811 q = 1) : d184227 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d129427, d184227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d129427, d184227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d129428 q = 1) (hb : d181811 q = 1) : d184228 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d129428, d184228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d129428, d184228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
end NetHack.Soko22Hazard87
