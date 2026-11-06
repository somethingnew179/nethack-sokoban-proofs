import NetHack.Soko22Hazard87.EqIntroBlocks0091
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro23000 (p : Pattern) (selected : d231384 p = 0) : d233263 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d19 q = 0) : d51871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20 q = 0) : d51872 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231383 q = 0) : d233262 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d231383, d233262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231383, d233262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231384 q = 0) : d233263 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d231384, d233263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231384, d233263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro23001 (p : Pattern) (selected : d231390 p = 0) : d233269 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231385 q = 0) : d233264 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231385, d233264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23000 q selected
    | true =>
      simp only [d231385, d233264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231386 q = 0) : d233265 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231386, d233265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231386, d233265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231387 q = 0) : d233266 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231387, d233266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231387, d233266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231388 q = 0) : d233267 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231388, d233267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231388, d233267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231389 q = 0) : d233268 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d231389, d233268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231389, d233268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231390 q = 0) : d233269 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231390, d233269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231390, d233269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23002 (p : Pattern) (selected : d231396 p = 0) : d233275 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231391 q = 0) : d233270 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231391, d233270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23001 q selected
    | true =>
      simp only [d231391, d233270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231392 q = 0) : d233271 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231392, d233271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231392, d233271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231393 q = 0) : d233272 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231393, d233272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231393, d233272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231394 q = 0) : d233273 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d231394, d233273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231394, d233273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231395 q = 0) : d233274 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d231395, d233274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231395, d233274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231396 q = 0) : d233275 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d231396, d233275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231396, d233275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23003 (p : Pattern) (selected : d231402 p = 0) : d233281 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231397 q = 0) : d233276 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231397, d233276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23002 q selected
    | true =>
      simp only [d231397, d233276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231398 q = 0) : d233277 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231398, d233277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231398, d233277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231399 q = 0) : d233278 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231399, d233278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231399, d233278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231400 q = 0) : d233279 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231400, d233279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231400, d233279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231401 q = 0) : d233280 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231401, d233280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231401, d233280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231402 q = 0) : d233281 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231402, d233281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231402, d233281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23004 (p : Pattern) (selected : d231408 p = 0) : d233287 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231403 q = 0) : d233282 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231403, d233282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23003 q selected
    | true =>
      simp only [d231403, d233282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231404 q = 0) : d233283 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231404, d233283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231404, d233283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231405 q = 0) : d233284 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231405, d233284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231405, d233284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231406 q = 0) : d233285 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231406, d233285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231406, d233285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231407 q = 0) : d233286 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231407, d233286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231407, d233286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231408 q = 0) : d233287 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231408, d233287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231408, d233287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23005 (p : Pattern) (selected : d231409 p = 0) : d233288 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231397 q = 0) : d233276 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231397, d233276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23002 q selected
    | true =>
      simp only [d231397, d233276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231398 q = 0) : d233277 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231398, d233277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231398, d233277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231399 q = 0) : d233278 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231399, d233278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231399, d233278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231400 q = 0) : d233279 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231400, d233279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231400, d233279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231401 q = 0) : d233280 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231401, d233280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231401, d233280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231409 q = 0) : d233288 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231409, d233288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231409, d233288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23006 (p : Pattern) (selected : d231415 p = 0) : d233294 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231403 q = 0) : d233282 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231403, d233282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23003 q selected
    | true =>
      simp only [d231403, d233282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231404 q = 0) : d233283 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231404, d233283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231404, d233283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231405 q = 0) : d233284 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231405, d233284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231405, d233284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231406 q = 0) : d233285 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231406, d233285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231406, d233285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231407 q = 0) : d233286 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231407, d233286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231407, d233286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231410 q = 0) : d233289 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231410, d233289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23005 q selected
    | true =>
      simp only [d231410, d233289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231411 q = 0) : d233290 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231411, d233290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231411, d233290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d231412 q = 0) : d233291 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231412, d233291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231412, d233291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d231413 q = 0) : d233292 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231413, d233292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231413, d233292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231414 q = 0) : d233293 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231414, d233293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231414, d233293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d231415 q = 0) : d233294 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231415, d233294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231415, d233294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro23007 (p : Pattern) (selected : d231420 p = 0) : d233299 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231410 q = 0) : d233289 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231410, d233289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23005 q selected
    | true =>
      simp only [d231410, d233289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231411 q = 0) : d233290 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231411, d233290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231411, d233290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231412 q = 0) : d233291 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231412, d233291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231412, d233291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231413 q = 0) : d233292 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231413, d233292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231413, d233292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231414 q = 0) : d233293 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231414, d233293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231414, d233293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231420 q = 0) : d233299 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231420, d233299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231420, d233299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23008 (p : Pattern) (selected : d231431 p = 0) : d233310 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231426 q = 0) : d233305 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231426, d233305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231426, d233305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23000 q selected
  have h2 (q : Pattern) (selected : d231385 q = 0) : d233264 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231385, d233264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23000 q selected
    | true =>
      simp only [d231385, d233264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231427 q = 0) : d233306 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231427, d233306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231427, d233306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231386 q = 0) : d233265 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231386, d233265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231386, d233265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231428 q = 0) : d233307 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231428, d233307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231428, d233307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231429 q = 0) : d233308 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231429, d233308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231429, d233308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231430 q = 0) : d233309 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d231430, d233309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231430, d233309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d231431 q = 0) : d233310 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231431, d233310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231431, d233310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23009 (p : Pattern) (selected : d231437 p = 0) : d233316 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231432 q = 0) : d233311 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231432, d233311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23008 q selected
    | true =>
      simp only [d231432, d233311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231433 q = 0) : d233312 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231433, d233312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231433, d233312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231434 q = 0) : d233313 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231434, d233313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231434, d233313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231435 q = 0) : d233314 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d231435, d233314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231435, d233314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231436 q = 0) : d233315 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d231436, d233315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231436, d233315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231437 q = 0) : d233316 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d231437, d233316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231437, d233316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23010 (p : Pattern) (selected : d231443 p = 0) : d233322 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231438 q = 0) : d233317 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231438, d233317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23009 q selected
    | true =>
      simp only [d231438, d233317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231439 q = 0) : d233318 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231439, d233318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231439, d233318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231440 q = 0) : d233319 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231440, d233319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231440, d233319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231441 q = 0) : d233320 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231441, d233320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231441, d233320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231442 q = 0) : d233321 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231442, d233321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231442, d233321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231443 q = 0) : d233322 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231443, d233322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231443, d233322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23011 (p : Pattern) (selected : d231449 p = 0) : d233328 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231444 q = 0) : d233323 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231444, d233323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23010 q selected
    | true =>
      simp only [d231444, d233323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231445 q = 0) : d233324 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231445, d233324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231445, d233324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231446 q = 0) : d233325 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231446, d233325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231446, d233325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231447 q = 0) : d233326 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231447, d233326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231447, d233326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231448 q = 0) : d233327 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231448, d233327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231448, d233327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231449 q = 0) : d233328 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231449, d233328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231449, d233328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23012 (p : Pattern) (selected : d231455 p = 0) : d233334 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231416 q = 0) : d233295 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231416, d233295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23004 q selected
    | true =>
      simp only [d231416, d233295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23006 q selected
  have h2 (q : Pattern) (selected : d231417 q = 0) : d233296 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231417, d233296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231417, d233296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231418 q = 0) : d233297 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231418, d233297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231418, d233297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231419 q = 0) : d233298 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231419, d233298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231419, d233298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231421 q = 0) : d233300 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231421, d233300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231421, d233300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23007 q selected
  have h6 (q : Pattern) (selected : d231422 q = 0) : d233301 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231422, d233301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231422, d233301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231423 q = 0) : d233302 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231423, d233302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231423, d233302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d231424 q = 0) : d233303 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231424, d233303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231424, d233303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d231425 q = 0) : d233304 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231425, d233304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231425, d233304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231450 q = 0) : d233329 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231450, d233329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231450, d233329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23011 q selected
  have h11 (q : Pattern) (selected : d231451 q = 0) : d233330 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231451, d233330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d231451, d233330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d231452 q = 0) : d233331 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231452, d233331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d231452, d233331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d231453 q = 0) : d233332 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231453, d233332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d231453, d233332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d231454 q = 0) : d233333 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231454, d233333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d231454, d233333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d231455 q = 0) : d233334 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d231455, d233334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d231455, d233334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro23013 (p : Pattern) (selected : d231465 p = 0) : d233344 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231403 q = 0) : d233282 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231403, d233282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23003 q selected
    | true =>
      simp only [d231403, d233282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231461 q = 0) : d233340 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231461, d233340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231461, d233340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231462 q = 0) : d233341 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231462, d233341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231462, d233341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231463 q = 0) : d233342 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231463, d233342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231463, d233342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231464 q = 0) : d233343 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231464, d233343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231464, d233343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231465 q = 0) : d233344 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231465, d233344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231465, d233344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23014 (p : Pattern) (selected : d231472 p = 0) : d233351 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231403 q = 0) : d233282 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231403, d233282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23003 q selected
    | true =>
      simp only [d231403, d233282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231461 q = 0) : d233340 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231461, d233340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231461, d233340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231462 q = 0) : d233341 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231462, d233341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231462, d233341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231463 q = 0) : d233342 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231463, d233342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231463, d233342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231464 q = 0) : d233343 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231464, d233343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231464, d233343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231410 q = 0) : d233289 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231410, d233289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23005 q selected
    | true =>
      simp only [d231410, d233289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231468 q = 0) : d233347 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231468, d233347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231468, d233347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231469 q = 0) : d233348 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231469, d233348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231469, d233348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d231470 q = 0) : d233349 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231470, d233349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231470, d233349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231471 q = 0) : d233350 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231471, d233350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231471, d233350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d231472 q = 0) : d233351 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231472, d233351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231472, d233351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro23015 (p : Pattern) (selected : d231477 p = 0) : d233356 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231397 q = 0) : d233276 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231397, d233276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23002 q selected
    | true =>
      simp only [d231397, d233276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231398 q = 0) : d233277 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231398, d233277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231398, d233277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231399 q = 0) : d233278 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231399, d233278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231399, d233278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231400 q = 0) : d233279 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231400, d233279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231400, d233279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231476 q = 0) : d233355 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231476, d233355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231476, d233355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231477 q = 0) : d233356 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231477, d233356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231477, d233356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23016 (p : Pattern) (selected : d231484 p = 0) : d233363 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231397 q = 0) : d233276 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231397, d233276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23002 q selected
    | true =>
      simp only [d231397, d233276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231398 q = 0) : d233277 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231398, d233277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231398, d233277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231399 q = 0) : d233278 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231399, d233278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231399, d233278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231482 q = 0) : d233361 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231482, d233361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231482, d233361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231483 q = 0) : d233362 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231483, d233362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231483, d233362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231484 q = 0) : d233363 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231484, d233363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231484, d233363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23017 (p : Pattern) (selected : d231489 p = 0) : d233368 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133 q = 0) : d51984 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro204 q selected
    | true =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d134 q = 0) : d51985 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231488 q = 0) : d233367 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d231488, d233367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231488, d233367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d19 q = 0) : d51871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20 q = 0) : d51872 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231383 q = 0) : d233262 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d231383, d233262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231383, d233262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231489 q = 0) : d233368 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d231489, d233368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231489, d233368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro23018 (p : Pattern) (selected : d231495 p = 0) : d233374 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231490 q = 0) : d233369 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231490, d233369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23017 q selected
    | true =>
      simp only [d231490, d233369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231491 q = 0) : d233370 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231491, d233370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231491, d233370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231492 q = 0) : d233371 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231492, d233371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231492, d233371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231493 q = 0) : d233372 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231493, d233372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231493, d233372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231385 q = 0) : d233264 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231385, d233264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23000 q selected
    | true =>
      simp only [d231385, d233264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231386 q = 0) : d233265 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231386, d233265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231386, d233265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231387 q = 0) : d233266 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231387, d233266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231387, d233266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231388 q = 0) : d233267 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231388, d233267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231388, d233267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d231494 q = 0) : d233373 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d231494, d233373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231494, d233373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231389 q = 0) : d233268 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d231389, d233268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d231389, d233268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d231495 q = 0) : d233374 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231495, d233374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d231495, d233374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro23019 (p : Pattern) (selected : d231501 p = 0) : d233380 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231496 q = 0) : d233375 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231496, d233375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23018 q selected
    | true =>
      simp only [d231496, d233375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23001 q selected
  have h2 (q : Pattern) (selected : d231497 q = 0) : d233376 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231497, d233376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231497, d233376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231498 q = 0) : d233377 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231498, d233377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231498, d233377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231391 q = 0) : d233270 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231391, d233270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23001 q selected
    | true =>
      simp only [d231391, d233270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231392 q = 0) : d233271 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231392, d233271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231392, d233271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231393 q = 0) : d233272 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231393, d233272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231393, d233272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231499 q = 0) : d233378 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d231499, d233378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231499, d233378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231394 q = 0) : d233273 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d231394, d233273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231394, d233273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d231500 q = 0) : d233379 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d231500, d233379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231500, d233379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231501 q = 0) : d233380 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d231501, d233380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d231501, d233380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro23020 (p : Pattern) (selected : d231507 p = 0) : d233386 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231502 q = 0) : d233381 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231502, d233381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23019 q selected
    | true =>
      simp only [d231502, d233381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231503 q = 0) : d233382 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231503, d233382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231503, d233382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231397 q = 0) : d233276 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231397, d233276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23002 q selected
    | true =>
      simp only [d231397, d233276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231398 q = 0) : d233277 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231398, d233277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231398, d233277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231504 q = 0) : d233383 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231504, d233383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231504, d233383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231505 q = 0) : d233384 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231505, d233384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231505, d233384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231506 q = 0) : d233385 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231506, d233385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231506, d233385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d231507 q = 0) : d233386 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231507, d233386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231507, d233386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23021 (p : Pattern) (selected : d231510 p = 0) : d233263 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164 q = 0) : d51871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
    | true =>
      simp only [d164, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d165 q = 0) : d51872 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d165, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d165, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231509 q = 0) : d233262 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d231509, d233262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231509, d233262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231510 q = 0) : d233263 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d231510, d233263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231510, d233263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro23022 (p : Pattern) (selected : d231516 p = 0) : d233269 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231511 q = 0) : d233264 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231511, d233264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23021 q selected
    | true =>
      simp only [d231511, d233264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231512 q = 0) : d233265 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231512, d233265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231512, d233265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231513 q = 0) : d233266 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231513, d233266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231513, d233266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231514 q = 0) : d233267 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231514, d233267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231514, d233267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231515 q = 0) : d233268 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d231515, d233268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231515, d233268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231516 q = 0) : d233269 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231516, d233269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231516, d233269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23023 (p : Pattern) (selected : d231522 p = 0) : d233275 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231517 q = 0) : d233270 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231517, d233270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23022 q selected
    | true =>
      simp only [d231517, d233270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231518 q = 0) : d233271 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231518, d233271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231518, d233271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231519 q = 0) : d233272 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231519, d233272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231519, d233272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231520 q = 0) : d233273 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d231520, d233273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231520, d233273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231521 q = 0) : d233274 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d231521, d233274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231521, d233274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231522 q = 0) : d233275 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d231522, d233275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231522, d233275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23024 (p : Pattern) (selected : d231528 p = 0) : d233281 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231523 q = 0) : d233276 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231523, d233276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23023 q selected
    | true =>
      simp only [d231523, d233276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231524 q = 0) : d233277 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231524, d233277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231524, d233277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231525 q = 0) : d233278 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231525, d233278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231525, d233278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231526 q = 0) : d233279 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231526, d233279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231526, d233279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231527 q = 0) : d233280 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231527, d233280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231527, d233280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231528 q = 0) : d233281 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231528, d233281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231528, d233281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23025 (p : Pattern) (selected : d231534 p = 0) : d233392 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231478 q = 0) : d233357 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231478, d233357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23015 q selected
    | true =>
      simp only [d231478, d233357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231479 q = 0) : d233358 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231479, d233358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231479, d233358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231480 q = 0) : d233359 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231480, d233359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231480, d233359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231481 q = 0) : d233360 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231481, d233360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231481, d233360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231485 q = 0) : d233364 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231485, d233364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23016 q selected
    | true =>
      simp only [d231485, d233364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231486 q = 0) : d233365 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231486, d233365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231486, d233365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231487 q = 0) : d233366 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231487, d233366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231487, d233366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d231508 q = 0) : d233387 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231508, d233387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23020 q selected
    | true =>
      simp only [d231508, d233387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23003 q selected
  have h9 (q : Pattern) (selected : d231529 q = 0) : d233282 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231529, d233282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23024 q selected
    | true =>
      simp only [d231529, d233282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d231530 q = 0) : d233388 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231530, d233388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d231530, d233388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d231403 q = 0) : d233282 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231403, d233282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23003 q selected
    | true =>
      simp only [d231403, d233282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d231404 q = 0) : d233283 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231404, d233283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d231404, d233283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d231531 q = 0) : d233389 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231531, d233389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d231531, d233389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d231532 q = 0) : d233390 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231532, d233390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231532, d233390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d231533 q = 0) : d233391 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231533, d233391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231533, d233391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d231534 q = 0) : d233392 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231534, d233392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231534, d233392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro23026 (p : Pattern) (selected : d231535 p = 0) : d233393 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231397 q = 0) : d233276 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231397, d233276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23002 q selected
    | true =>
      simp only [d231397, d233276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231398 q = 0) : d233277 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231398, d233277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231398, d233277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231399 q = 0) : d233278 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231399, d233278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231399, d233278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231400 q = 0) : d233279 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231400, d233279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231400, d233279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231476 q = 0) : d233355 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231476, d233355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231476, d233355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231535 q = 0) : d233393 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231535, d233393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231535, d233393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23027 (p : Pattern) (selected : d231540 p = 0) : d233398 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231397 q = 0) : d233276 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231397, d233276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23002 q selected
    | true =>
      simp only [d231397, d233276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231398 q = 0) : d233277 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231398, d233277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231398, d233277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231399 q = 0) : d233278 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231399, d233278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231399, d233278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231482 q = 0) : d233361 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231482, d233361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231482, d233361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231483 q = 0) : d233362 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231483, d233362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231483, d233362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231540 q = 0) : d233398 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231540, d233398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231540, d233398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23028 (p : Pattern) (selected : d231544 p = 0) : d233402 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231502 q = 0) : d233381 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231502, d233381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23019 q selected
    | true =>
      simp only [d231502, d233381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231503 q = 0) : d233382 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231503, d233382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231503, d233382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231397 q = 0) : d233276 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231397, d233276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23002 q selected
    | true =>
      simp only [d231397, d233276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231398 q = 0) : d233277 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231398, d233277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231398, d233277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231504 q = 0) : d233383 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231504, d233383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231504, d233383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231505 q = 0) : d233384 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231505, d233384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231505, d233384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231506 q = 0) : d233385 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231506, d233385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231506, d233385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d231544 q = 0) : d233402 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231544, d233402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231544, d233402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23029 (p : Pattern) (selected : d231546 p = 0) : d233288 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231523 q = 0) : d233276 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231523, d233276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23023 q selected
    | true =>
      simp only [d231523, d233276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231524 q = 0) : d233277 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231524, d233277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231524, d233277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231525 q = 0) : d233278 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231525, d233278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231525, d233278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231526 q = 0) : d233279 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231526, d233279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231526, d233279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231527 q = 0) : d233280 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231527, d233280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231527, d233280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231546 q = 0) : d233288 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231546, d233288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231546, d233288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23030 (p : Pattern) (selected : d231552 p = 0) : d233408 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231478 q = 0) : d233357 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231478, d233357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23015 q selected
    | true =>
      simp only [d231478, d233357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231479 q = 0) : d233358 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231479, d233358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231479, d233358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231480 q = 0) : d233359 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231480, d233359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231480, d233359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231481 q = 0) : d233360 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231481, d233360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231481, d233360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231485 q = 0) : d233364 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231485, d233364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23016 q selected
    | true =>
      simp only [d231485, d233364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231486 q = 0) : d233365 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231486, d233365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231486, d233365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231487 q = 0) : d233366 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231487, d233366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231487, d233366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d231508 q = 0) : d233387 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231508, d233387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23020 q selected
    | true =>
      simp only [d231508, d233387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23003 q selected
  have h9 (q : Pattern) (selected : d231529 q = 0) : d233282 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231529, d233282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23024 q selected
    | true =>
      simp only [d231529, d233282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d231530 q = 0) : d233388 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231530, d233388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d231530, d233388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d231403 q = 0) : d233282 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231403, d233282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23003 q selected
    | true =>
      simp only [d231403, d233282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d231404 q = 0) : d233283 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231404, d233283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d231404, d233283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d231531 q = 0) : d233389 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231531, d233389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d231531, d233389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d231532 q = 0) : d233390 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231532, d233390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231532, d233390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d231533 q = 0) : d233391 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231533, d233391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231533, d233391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d231536 q = 0) : d233394 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231536, d233394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23026 q selected
    | true =>
      simp only [d231536, d233394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d231537 q = 0) : d233395 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231537, d233395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231537, d233395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d231538 q = 0) : d233396 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231538, d233396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d231538, d233396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d231539 q = 0) : d233397 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231539, d233397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231539, d233397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d231541 q = 0) : d233399 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231541, d233399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23027 q selected
    | true =>
      simp only [d231541, d233399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d231542 q = 0) : d233400 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231542, d233400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231542, d233400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d231543 q = 0) : d233401 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231543, d233401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d231543, d233401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d231545 q = 0) : d233403 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231545, d233403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23028 q selected
    | true =>
      simp only [d231545, d233403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23005 q selected
  have h24 (q : Pattern) (selected : d231547 q = 0) : d233289 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231547, d233289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23029 q selected
    | true =>
      simp only [d231547, d233289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d231548 q = 0) : d233404 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231548, d233404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d231548, d233404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d231410 q = 0) : d233289 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231410, d233289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23005 q selected
    | true =>
      simp only [d231410, d233289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d231411 q = 0) : d233290 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231411, d233290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d231411, d233290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d231549 q = 0) : d233405 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231549, d233405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d231549, d233405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d231550 q = 0) : d233406 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231550, d233406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d231550, d233406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d231551 q = 0) : d233407 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231551, d233407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d231551, d233407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d231552 q = 0) : d233408 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231552, d233408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d231552, d233408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro23031 (p : Pattern) (selected : d231554 p = 0) : d233410 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231403 q = 0) : d233282 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231403, d233282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23003 q selected
    | true =>
      simp only [d231403, d233282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231461 q = 0) : d233340 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231461, d233340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231461, d233340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231462 q = 0) : d233341 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231462, d233341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231462, d233341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231463 q = 0) : d233342 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231463, d233342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231463, d233342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231464 q = 0) : d233343 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231464, d233343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231464, d233343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231554 q = 0) : d233410 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231554, d233410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231554, d233410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23032 (p : Pattern) (selected : d231561 p = 0) : d233417 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231545 q = 0) : d233403 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231545, d233403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23028 q selected
    | true =>
      simp only [d231545, d233403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23005 q selected
  have h2 (q : Pattern) (selected : d231547 q = 0) : d233289 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231547, d233289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23029 q selected
    | true =>
      simp only [d231547, d233289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231548 q = 0) : d233404 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231548, d233404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231548, d233404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231410 q = 0) : d233289 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231410, d233289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23005 q selected
    | true =>
      simp only [d231410, d233289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231411 q = 0) : d233290 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231411, d233290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231411, d233290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231549 q = 0) : d233405 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231549, d233405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231549, d233405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231559 q = 0) : d233415 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231559, d233415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231559, d233415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231560 q = 0) : d233416 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231560, d233416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231560, d233416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d231561 q = 0) : d233417 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231561, d233417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231561, d233417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro23033 (p : Pattern) (selected : d231572 p = 0) : d233428 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231567 q = 0) : d233423 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231567, d233423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231567, d233423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23017 q selected
  have h2 (q : Pattern) (selected : d231490 q = 0) : d233369 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231490, d233369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23017 q selected
    | true =>
      simp only [d231490, d233369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231568 q = 0) : d233424 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231568, d233424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231568, d233424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231491 q = 0) : d233370 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231491, d233370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231491, d233370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231569 q = 0) : d233425 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231569, d233425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231569, d233425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231570 q = 0) : d233426 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231570, d233426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231570, d233426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231426 q = 0) : d233305 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231426, d233305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231426, d233305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23000 q selected
  have h8 (q : Pattern) (selected : d231385 q = 0) : d233264 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231385, d233264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23000 q selected
    | true =>
      simp only [d231385, d233264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d231427 q = 0) : d233306 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231427, d233306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231427, d233306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231386 q = 0) : d233265 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231386, d233265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d231386, d233265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d231428 q = 0) : d233307 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231428, d233307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d231428, d233307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d231429 q = 0) : d233308 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231429, d233308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d231429, d233308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d231571 q = 0) : d233427 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d231571, d233427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231571, d233427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d231430 q = 0) : d233309 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d231430, d233309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d231430, d233309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d231572 q = 0) : d233428 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231572, d233428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d231572, d233428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro23034 (p : Pattern) (selected : d231578 p = 0) : d233434 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231573 q = 0) : d233429 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231573, d233429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23033 q selected
    | true =>
      simp only [d231573, d233429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23008 q selected
  have h2 (q : Pattern) (selected : d231574 q = 0) : d233430 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231574, d233430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231574, d233430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231575 q = 0) : d233431 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231575, d233431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231575, d233431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231432 q = 0) : d233311 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231432, d233311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23008 q selected
    | true =>
      simp only [d231432, d233311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231433 q = 0) : d233312 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231433, d233312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231433, d233312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231434 q = 0) : d233313 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231434, d233313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231434, d233313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231576 q = 0) : d233432 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d231576, d233432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231576, d233432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231435 q = 0) : d233314 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d231435, d233314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231435, d233314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d231577 q = 0) : d233433 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d231577, d233433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231577, d233433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231578 q = 0) : d233434 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d231578, d233434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d231578, d233434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro23035 (p : Pattern) (selected : d231584 p = 0) : d233440 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231579 q = 0) : d233435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231579, d233435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23034 q selected
    | true =>
      simp only [d231579, d233435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231580 q = 0) : d233436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231580, d233436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231580, d233436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231438 q = 0) : d233317 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231438, d233317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23009 q selected
    | true =>
      simp only [d231438, d233317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231439 q = 0) : d233318 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231439, d233318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231439, d233318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231581 q = 0) : d233437 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231581, d233437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231581, d233437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231582 q = 0) : d233438 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231582, d233438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231582, d233438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231583 q = 0) : d233439 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231583, d233439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231583, d233439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d231584 q = 0) : d233440 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231584, d233440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231584, d233440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23036 (p : Pattern) (selected : d231591 p = 0) : d233310 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231586 q = 0) : d233305 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231586, d233305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231586, d233305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23021 q selected
  have h2 (q : Pattern) (selected : d231511 q = 0) : d233264 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231511, d233264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23021 q selected
    | true =>
      simp only [d231511, d233264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231587 q = 0) : d233306 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231587, d233306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231587, d233306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231512 q = 0) : d233265 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231512, d233265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231512, d233265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231588 q = 0) : d233307 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231588, d233307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231588, d233307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231589 q = 0) : d233308 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231589, d233308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231589, d233308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231590 q = 0) : d233309 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d231590, d233309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231590, d233309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d231591 q = 0) : d233310 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231591, d233310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231591, d233310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23037 (p : Pattern) (selected : d231597 p = 0) : d233316 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231592 q = 0) : d233311 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231592, d233311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23036 q selected
    | true =>
      simp only [d231592, d233311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231593 q = 0) : d233312 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231593, d233312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231593, d233312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231594 q = 0) : d233313 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231594, d233313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231594, d233313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231595 q = 0) : d233314 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d231595, d233314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231595, d233314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231596 q = 0) : d233315 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d231596, d233315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231596, d233315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231597 q = 0) : d233316 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d231597, d233316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231597, d233316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23038 (p : Pattern) (selected : d231603 p = 0) : d233322 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231598 q = 0) : d233317 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231598, d233317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23037 q selected
    | true =>
      simp only [d231598, d233317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231599 q = 0) : d233318 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231599, d233318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231599, d233318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231600 q = 0) : d233319 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231600, d233319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231600, d233319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231601 q = 0) : d233320 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231601, d233320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231601, d233320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231602 q = 0) : d233321 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231602, d233321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231602, d233321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231603 q = 0) : d233322 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231603, d233322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231603, d233322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23039 (p : Pattern) (selected : d231609 p = 0) : d233446 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231585 q = 0) : d233441 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231585, d233441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23035 q selected
    | true =>
      simp only [d231585, d233441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23010 q selected
  have h2 (q : Pattern) (selected : d231604 q = 0) : d233323 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231604, d233323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23038 q selected
    | true =>
      simp only [d231604, d233323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231605 q = 0) : d233442 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231605, d233442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231605, d233442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231444 q = 0) : d233323 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231444, d233323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23010 q selected
    | true =>
      simp only [d231444, d233323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231445 q = 0) : d233324 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231445, d233324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231445, d233324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231606 q = 0) : d233443 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231606, d233443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231606, d233443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231607 q = 0) : d233444 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231607, d233444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231607, d233444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231608 q = 0) : d233445 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231608, d233445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231608, d233445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d231609 q = 0) : d233446 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231609, d233446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231609, d233446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro23040 (p : Pattern) (selected : d231615 p = 0) : d233452 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231466 q = 0) : d233345 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231466, d233345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231466, d233345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23013 q selected
  have h2 (q : Pattern) (selected : d231467 q = 0) : d233346 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231467, d233346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231467, d233346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231473 q = 0) : d233352 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231473, d233352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23013 q selected
    | true =>
      simp only [d231473, d233352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23014 q selected
  have h4 (q : Pattern) (selected : d231474 q = 0) : d233353 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231474, d233353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231474, d233353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231475 q = 0) : d233354 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231475, d233354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231475, d233354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231553 q = 0) : d233409 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231553, d233409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23025 q selected
    | true =>
      simp only [d231553, d233409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23030 q selected
  have h7 (q : Pattern) (selected : d231555 q = 0) : d233411 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231555, d233411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23031 q selected
    | true =>
      simp only [d231555, d233411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d231556 q = 0) : d233412 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231556, d233412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231556, d233412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d231557 q = 0) : d233413 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231557, d233413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d231557, d233413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d231558 q = 0) : d233414 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231558, d233414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231558, d233414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d231562 q = 0) : d233418 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231562, d233418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231562, d233418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23032 q selected
  have h12 (q : Pattern) (selected : d231563 q = 0) : d233419 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231563, d233419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d231563, d233419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d231564 q = 0) : d233420 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231564, d233420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d231564, d233420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d231565 q = 0) : d233421 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231565, d233421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d231565, d233421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d231566 q = 0) : d233422 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231566, d233422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d231566, d233422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d231610 q = 0) : d233447 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231610, d233447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231610, d233447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23039 q selected
  have h17 (q : Pattern) (selected : d231611 q = 0) : d233448 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231611, d233448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d231611, d233448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d231612 q = 0) : d233449 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231612, d233449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d231612, d233449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d231613 q = 0) : d233450 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231613, d233450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d231613, d233450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d231614 q = 0) : d233451 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231614, d233451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d231614, d233451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d231615 q = 0) : d233452 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d231615, d233452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d231615, d233452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro23041 (p : Pattern) (selected : d231621 p = 0) : d233458 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231456 q = 0) : d233335 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d231456, d233335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231456, d233335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23012 q selected
  have h2 (q : Pattern) (selected : d231457 q = 0) : d233336 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d231457, d233336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231457, d233336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231458 q = 0) : d233337 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d231458, d233337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231458, d233337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231459 q = 0) : d233338 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d231459, d233338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231459, d233338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231460 q = 0) : d233339 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d231460, d233339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231460, d233339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231616 q = 0) : d233453 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d231616, d233453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231616, d233453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23040 q selected
  have h7 (q : Pattern) (selected : d231617 q = 0) : d233454 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d231617, d233454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231617, d233454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231618 q = 0) : d233455 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d231618, d233455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231618, d233455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d231619 q = 0) : d233456 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d231619, d233456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231619, d233456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231620 q = 0) : d233457 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d231620, d233457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231620, d233457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d231621 q = 0) : d233458 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d231621, d233458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231621, d233458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro23042 (p : Pattern) (selected : d231626 p = 0) : d233463 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231508 q = 0) : d233387 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231508, d233387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23020 q selected
    | true =>
      simp only [d231508, d233387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23003 q selected
  have h2 (q : Pattern) (selected : d231622 q = 0) : d233459 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231622, d233459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231622, d233459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231623 q = 0) : d233460 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231623, d233460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231623, d233460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231624 q = 0) : d233461 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231624, d233461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231624, d233461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231625 q = 0) : d233462 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231625, d233462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231625, d233462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231626 q = 0) : d233463 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231626, d233463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231626, d233463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23043 (p : Pattern) (selected : d231633 p = 0) : d233470 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231508 q = 0) : d233387 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231508, d233387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23020 q selected
    | true =>
      simp only [d231508, d233387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23003 q selected
  have h2 (q : Pattern) (selected : d231622 q = 0) : d233459 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231622, d233459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231622, d233459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231623 q = 0) : d233460 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231623, d233460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231623, d233460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231624 q = 0) : d233461 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231624, d233461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231624, d233461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231625 q = 0) : d233462 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231625, d233462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231625, d233462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231545 q = 0) : d233403 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231545, d233403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23028 q selected
    | true =>
      simp only [d231545, d233403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23005 q selected
  have h7 (q : Pattern) (selected : d231629 q = 0) : d233466 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231629, d233466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231629, d233466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231630 q = 0) : d233467 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231630, d233467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231630, d233467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d231631 q = 0) : d233468 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231631, d233468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231631, d233468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231632 q = 0) : d233469 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231632, d233469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231632, d233469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d231633 q = 0) : d233470 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231633, d233470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231633, d233470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro23044 (p : Pattern) (selected : d231638 p = 0) : d233475 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231502 q = 0) : d233381 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231502, d233381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23019 q selected
    | true =>
      simp only [d231502, d233381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231503 q = 0) : d233382 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231503, d233382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231503, d233382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231397 q = 0) : d233276 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231397, d233276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23002 q selected
    | true =>
      simp only [d231397, d233276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231398 q = 0) : d233277 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231398, d233277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231398, d233277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231504 q = 0) : d233383 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231504, d233383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231504, d233383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231505 q = 0) : d233384 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231505, d233384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231505, d233384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231637 q = 0) : d233474 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231637, d233474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231637, d233474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231638 q = 0) : d233475 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231638, d233475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231638, d233475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23045 (p : Pattern) (selected : d231645 p = 0) : d233482 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231502 q = 0) : d233381 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231502, d233381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23019 q selected
    | true =>
      simp only [d231502, d233381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231503 q = 0) : d233382 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231503, d233382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231503, d233382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231397 q = 0) : d233276 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231397, d233276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23002 q selected
    | true =>
      simp only [d231397, d233276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231398 q = 0) : d233277 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231398, d233277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231398, d233277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231504 q = 0) : d233383 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231504, d233383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231504, d233383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231643 q = 0) : d233480 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231643, d233480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231643, d233480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231644 q = 0) : d233481 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231644, d233481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231644, d233481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d231645 q = 0) : d233482 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231645, d233482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231645, d233482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23046 (p : Pattern) (selected : d231650 p = 0) : d233487 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d313 q = 0) : d52112 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d52112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro234 q selected
    | true =>
      simp only [d313, d52112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d314 q = 0) : d52113 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d52113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d314, d52113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231649 q = 0) : d233486 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d231649, d233486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231649, d233486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133 q = 0) : d51984 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro204 q selected
    | true =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d134 q = 0) : d51985 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231488 q = 0) : d233367 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d231488, d233367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231488, d233367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231650 q = 0) : d233487 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d231650, d233487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231650, d233487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro23047 (p : Pattern) (selected : d231656 p = 0) : d233493 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231651 q = 0) : d233488 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231651, d233488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23046 q selected
    | true =>
      simp only [d231651, d233488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231652 q = 0) : d233489 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231652, d233489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231652, d233489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231653 q = 0) : d233490 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231653, d233490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231653, d233490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231654 q = 0) : d233491 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231654, d233491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231654, d233491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231490 q = 0) : d233369 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231490, d233369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23017 q selected
    | true =>
      simp only [d231490, d233369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231491 q = 0) : d233370 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231491, d233370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231491, d233370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231492 q = 0) : d233371 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231492, d233371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231492, d233371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231493 q = 0) : d233372 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231493, d233372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231493, d233372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d231655 q = 0) : d233492 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d231655, d233492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231655, d233492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231385 q = 0) : d233264 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231385, d233264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23000 q selected
    | true =>
      simp only [d231385, d233264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d231386 q = 0) : d233265 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231386, d233265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d231386, d233265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d231387 q = 0) : d233266 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231387, d233266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231387, d233266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d231388 q = 0) : d233267 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231388, d233267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d231388, d233267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d231494 q = 0) : d233373 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d231494, d233373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d231494, d233373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d231656 q = 0) : d233493 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231656, d233493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d231656, d233493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro23048 (p : Pattern) (selected : d231662 p = 0) : d233499 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231657 q = 0) : d233494 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231657, d233494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23047 q selected
    | true =>
      simp only [d231657, d233494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23018 q selected
  have h2 (q : Pattern) (selected : d231658 q = 0) : d233495 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231658, d233495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231658, d233495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231659 q = 0) : d233496 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231659, d233496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231659, d233496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231496 q = 0) : d233375 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231496, d233375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23018 q selected
    | true =>
      simp only [d231496, d233375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23001 q selected
  have h5 (q : Pattern) (selected : d231497 q = 0) : d233376 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231497, d233376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231497, d233376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231498 q = 0) : d233377 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231498, d233377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231498, d233377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231660 q = 0) : d233497 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d231660, d233497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231660, d233497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231391 q = 0) : d233270 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231391, d233270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23001 q selected
    | true =>
      simp only [d231391, d233270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d231392 q = 0) : d233271 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231392, d233271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231392, d233271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231393 q = 0) : d233272 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231393, d233272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231393, d233272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d231499 q = 0) : d233378 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d231499, d233378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231499, d233378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d231661 q = 0) : d233498 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d231661, d233498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231661, d233498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d231662 q = 0) : d233499 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d231662, d233499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d231662, d233499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro23049 (p : Pattern) (selected : d231668 p = 0) : d233505 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231663 q = 0) : d233500 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231663, d233500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23048 q selected
    | true =>
      simp only [d231663, d233500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231664 q = 0) : d233501 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231664, d233501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231664, d233501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231502 q = 0) : d233381 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231502, d233381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23019 q selected
    | true =>
      simp only [d231502, d233381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231503 q = 0) : d233382 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231503, d233382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231503, d233382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231665 q = 0) : d233502 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231665, d233502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231665, d233502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231666 q = 0) : d233503 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231666, d233503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231666, d233503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231667 q = 0) : d233504 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231667, d233504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231667, d233504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d231668 q = 0) : d233505 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231668, d233505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231668, d233505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23050 (p : Pattern) (selected : d231671 p = 0) : d233368 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d344 q = 0) : d51984 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d344, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro239 q selected
    | true =>
      simp only [d344, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d345 q = 0) : d51985 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d345, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231670 q = 0) : d233367 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d231670, d233367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231670, d233367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164 q = 0) : d51871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
    | true =>
      simp only [d164, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d165 q = 0) : d51872 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d165, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d165, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231509 q = 0) : d233262 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d231509, d233262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231509, d233262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231671 q = 0) : d233368 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d231671, d233368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231671, d233368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro23051 (p : Pattern) (selected : d231677 p = 0) : d233374 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231672 q = 0) : d233369 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231672, d233369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23050 q selected
    | true =>
      simp only [d231672, d233369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231673 q = 0) : d233370 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231673, d233370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231673, d233370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231674 q = 0) : d233371 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231674, d233371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231674, d233371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231675 q = 0) : d233372 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231675, d233372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231675, d233372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231511 q = 0) : d233264 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231511, d233264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23021 q selected
    | true =>
      simp only [d231511, d233264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231512 q = 0) : d233265 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231512, d233265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231512, d233265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231513 q = 0) : d233266 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231513, d233266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231513, d233266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231514 q = 0) : d233267 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231514, d233267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231514, d233267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d231676 q = 0) : d233373 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d231676, d233373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231676, d233373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231515 q = 0) : d233268 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d231515, d233268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d231515, d233268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d231677 q = 0) : d233374 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231677, d233374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d231677, d233374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro23052 (p : Pattern) (selected : d231683 p = 0) : d233380 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231678 q = 0) : d233375 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231678, d233375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23051 q selected
    | true =>
      simp only [d231678, d233375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23022 q selected
  have h2 (q : Pattern) (selected : d231679 q = 0) : d233376 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231679, d233376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231679, d233376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231680 q = 0) : d233377 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231680, d233377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231680, d233377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231517 q = 0) : d233270 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231517, d233270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23022 q selected
    | true =>
      simp only [d231517, d233270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231518 q = 0) : d233271 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231518, d233271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231518, d233271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231519 q = 0) : d233272 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231519, d233272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231519, d233272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231681 q = 0) : d233378 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d231681, d233378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231681, d233378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231520 q = 0) : d233273 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d231520, d233273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231520, d233273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d231682 q = 0) : d233379 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d231682, d233379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231682, d233379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231683 q = 0) : d233380 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d231683, d233380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d231683, d233380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro23053 (p : Pattern) (selected : d231689 p = 0) : d233386 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231684 q = 0) : d233381 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231684, d233381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23052 q selected
    | true =>
      simp only [d231684, d233381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231685 q = 0) : d233382 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231685, d233382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231685, d233382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231523 q = 0) : d233276 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231523, d233276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23023 q selected
    | true =>
      simp only [d231523, d233276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231524 q = 0) : d233277 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231524, d233277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231524, d233277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231686 q = 0) : d233383 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231686, d233383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231686, d233383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231687 q = 0) : d233384 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231687, d233384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231687, d233384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231688 q = 0) : d233385 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231688, d233385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231688, d233385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d231689 q = 0) : d233386 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231689, d233386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231689, d233386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23054 (p : Pattern) (selected : d231695 p = 0) : d233511 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231502 q = 0) : d233381 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231502, d233381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23019 q selected
    | true =>
      simp only [d231502, d233381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231503 q = 0) : d233382 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231503, d233382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231503, d233382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231692 q = 0) : d233508 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231692, d233508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231692, d233508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231693 q = 0) : d233509 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231693, d233509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231693, d233509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231694 q = 0) : d233510 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231694, d233510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231694, d233510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231695 q = 0) : d233511 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231695, d233511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231695, d233511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23055 (p : Pattern) (selected : d231701 p = 0) : d233517 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231639 q = 0) : d233476 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231639, d233476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23044 q selected
    | true =>
      simp only [d231639, d233476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23015 q selected
  have h2 (q : Pattern) (selected : d231640 q = 0) : d233477 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231640, d233477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231640, d233477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231641 q = 0) : d233478 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231641, d233478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231641, d233478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231642 q = 0) : d233479 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231642, d233479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231642, d233479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231646 q = 0) : d233483 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231646, d233483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23045 q selected
    | true =>
      simp only [d231646, d233483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23016 q selected
  have h6 (q : Pattern) (selected : d231647 q = 0) : d233484 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231647, d233484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231647, d233484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231648 q = 0) : d233485 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231648, d233485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231648, d233485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d231669 q = 0) : d233506 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231669, d233506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23049 q selected
    | true =>
      simp only [d231669, d233506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23020 q selected
  have h9 (q : Pattern) (selected : d231690 q = 0) : d233387 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231690, d233387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23053 q selected
    | true =>
      simp only [d231690, d233387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23024 q selected
  have h10 (q : Pattern) (selected : d231691 q = 0) : d233507 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231691, d233507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d231691, d233507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d231696 q = 0) : d233512 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231696, d233512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23054 q selected
    | true =>
      simp only [d231696, d233512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d231697 q = 0) : d233513 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231697, d233513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d231697, d233513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d231698 q = 0) : d233514 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231698, d233514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d231698, d233514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d231699 q = 0) : d233515 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231699, d233515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231699, d233515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d231700 q = 0) : d233516 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231700, d233516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231700, d233516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d231701 q = 0) : d233517 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231701, d233517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231701, d233517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro23056 (p : Pattern) (selected : d231702 p = 0) : d233518 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231502 q = 0) : d233381 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231502, d233381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23019 q selected
    | true =>
      simp only [d231502, d233381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231503 q = 0) : d233382 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231503, d233382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231503, d233382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231397 q = 0) : d233276 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231397, d233276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23002 q selected
    | true =>
      simp only [d231397, d233276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231398 q = 0) : d233277 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231398, d233277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231398, d233277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231504 q = 0) : d233383 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231504, d233383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231504, d233383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231505 q = 0) : d233384 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231505, d233384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231505, d233384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231637 q = 0) : d233474 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231637, d233474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231637, d233474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231702 q = 0) : d233518 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231702, d233518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231702, d233518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23057 (p : Pattern) (selected : d231707 p = 0) : d233523 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231502 q = 0) : d233381 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231502, d233381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23019 q selected
    | true =>
      simp only [d231502, d233381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231503 q = 0) : d233382 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231503, d233382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231503, d233382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231397 q = 0) : d233276 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231397, d233276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23002 q selected
    | true =>
      simp only [d231397, d233276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231398 q = 0) : d233277 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231398, d233277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231398, d233277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231504 q = 0) : d233383 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231504, d233383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231504, d233383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231643 q = 0) : d233480 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231643, d233480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231643, d233480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231644 q = 0) : d233481 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231644, d233481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231644, d233481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d231707 q = 0) : d233523 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231707, d233523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231707, d233523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23058 (p : Pattern) (selected : d231711 p = 0) : d233527 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231663 q = 0) : d233500 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231663, d233500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23048 q selected
    | true =>
      simp only [d231663, d233500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231664 q = 0) : d233501 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231664, d233501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231664, d233501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231502 q = 0) : d233381 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231502, d233381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23019 q selected
    | true =>
      simp only [d231502, d233381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231503 q = 0) : d233382 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231503, d233382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231503, d233382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231665 q = 0) : d233502 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231665, d233502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231665, d233502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231666 q = 0) : d233503 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231666, d233503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231666, d233503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231667 q = 0) : d233504 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231667, d233504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231667, d233504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d231711 q = 0) : d233527 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231711, d233527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231711, d233527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23059 (p : Pattern) (selected : d231713 p = 0) : d233402 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231684 q = 0) : d233381 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231684, d233381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23052 q selected
    | true =>
      simp only [d231684, d233381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231685 q = 0) : d233382 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231685, d233382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231685, d233382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231523 q = 0) : d233276 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231523, d233276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23023 q selected
    | true =>
      simp only [d231523, d233276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231524 q = 0) : d233277 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231524, d233277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231524, d233277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231686 q = 0) : d233383 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231686, d233383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231686, d233383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231687 q = 0) : d233384 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231687, d233384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231687, d233384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231688 q = 0) : d233385 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231688, d233385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231688, d233385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d231713 q = 0) : d233402 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231713, d233402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231713, d233402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23060 (p : Pattern) (selected : d231716 p = 0) : d233530 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231502 q = 0) : d233381 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231502, d233381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23019 q selected
    | true =>
      simp only [d231502, d233381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231503 q = 0) : d233382 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231503, d233382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231503, d233382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231692 q = 0) : d233508 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231692, d233508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231692, d233508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231693 q = 0) : d233509 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231693, d233509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231693, d233509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231694 q = 0) : d233510 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231694, d233510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231694, d233510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231716 q = 0) : d233530 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231716, d233530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231716, d233530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23061 (p : Pattern) (selected : d231722 p = 0) : d233536 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231639 q = 0) : d233476 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231639, d233476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23044 q selected
    | true =>
      simp only [d231639, d233476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23015 q selected
  have h2 (q : Pattern) (selected : d231640 q = 0) : d233477 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231640, d233477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231640, d233477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231641 q = 0) : d233478 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231641, d233478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231641, d233478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231642 q = 0) : d233479 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231642, d233479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231642, d233479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231646 q = 0) : d233483 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231646, d233483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23045 q selected
    | true =>
      simp only [d231646, d233483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23016 q selected
  have h6 (q : Pattern) (selected : d231647 q = 0) : d233484 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231647, d233484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231647, d233484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231648 q = 0) : d233485 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231648, d233485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231648, d233485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d231669 q = 0) : d233506 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231669, d233506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23049 q selected
    | true =>
      simp only [d231669, d233506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23020 q selected
  have h9 (q : Pattern) (selected : d231690 q = 0) : d233387 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231690, d233387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23053 q selected
    | true =>
      simp only [d231690, d233387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23024 q selected
  have h10 (q : Pattern) (selected : d231691 q = 0) : d233507 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231691, d233507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d231691, d233507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d231696 q = 0) : d233512 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231696, d233512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23054 q selected
    | true =>
      simp only [d231696, d233512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d231697 q = 0) : d233513 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231697, d233513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d231697, d233513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d231698 q = 0) : d233514 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231698, d233514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d231698, d233514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d231699 q = 0) : d233515 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231699, d233515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231699, d233515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d231700 q = 0) : d233516 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231700, d233516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231700, d233516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d231703 q = 0) : d233519 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231703, d233519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23056 q selected
    | true =>
      simp only [d231703, d233519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23026 q selected
  have h17 (q : Pattern) (selected : d231704 q = 0) : d233520 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231704, d233520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231704, d233520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d231705 q = 0) : d233521 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231705, d233521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d231705, d233521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d231706 q = 0) : d233522 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231706, d233522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231706, d233522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d231708 q = 0) : d233524 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231708, d233524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23057 q selected
    | true =>
      simp only [d231708, d233524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23027 q selected
  have h21 (q : Pattern) (selected : d231709 q = 0) : d233525 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231709, d233525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231709, d233525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d231710 q = 0) : d233526 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231710, d233526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d231710, d233526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d231712 q = 0) : d233528 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231712, d233528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23058 q selected
    | true =>
      simp only [d231712, d233528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23028 q selected
  have h24 (q : Pattern) (selected : d231714 q = 0) : d233403 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231714, d233403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23059 q selected
    | true =>
      simp only [d231714, d233403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23029 q selected
  have h25 (q : Pattern) (selected : d231715 q = 0) : d233529 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231715, d233529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d231715, d233529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d231717 q = 0) : d233531 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231717, d233531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23060 q selected
    | true =>
      simp only [d231717, d233531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d231718 q = 0) : d233532 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231718, d233532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d231718, d233532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d231719 q = 0) : d233533 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231719, d233533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d231719, d233533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d231720 q = 0) : d233534 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231720, d233534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d231720, d233534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d231721 q = 0) : d233535 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231721, d233535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d231721, d233535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d231722 q = 0) : d233536 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231722, d233536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d231722, d233536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro23062 (p : Pattern) (selected : d231724 p = 0) : d233538 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231508 q = 0) : d233387 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231508, d233387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23020 q selected
    | true =>
      simp only [d231508, d233387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23003 q selected
  have h2 (q : Pattern) (selected : d231622 q = 0) : d233459 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231622, d233459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231622, d233459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231623 q = 0) : d233460 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231623, d233460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231623, d233460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231624 q = 0) : d233461 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231624, d233461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231624, d233461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231625 q = 0) : d233462 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231625, d233462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231625, d233462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231403 q = 0) : d233282 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231403, d233282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23003 q selected
    | true =>
      simp only [d231403, d233282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231461 q = 0) : d233340 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231461, d233340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231461, d233340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231462 q = 0) : d233341 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231462, d233341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231462, d233341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d231463 q = 0) : d233342 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231463, d233342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231463, d233342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231464 q = 0) : d233343 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231464, d233343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231464, d233343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d231724 q = 0) : d233538 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231724, d233538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231724, d233538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro23063 (p : Pattern) (selected : d231731 p = 0) : d233545 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231712 q = 0) : d233528 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231712, d233528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23058 q selected
    | true =>
      simp only [d231712, d233528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23028 q selected
  have h2 (q : Pattern) (selected : d231714 q = 0) : d233403 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231714, d233403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23059 q selected
    | true =>
      simp only [d231714, d233403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23029 q selected
  have h3 (q : Pattern) (selected : d231715 q = 0) : d233529 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231715, d233529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231715, d233529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231717 q = 0) : d233531 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231717, d233531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23060 q selected
    | true =>
      simp only [d231717, d233531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231718 q = 0) : d233532 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231718, d233532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231718, d233532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231719 q = 0) : d233533 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231719, d233533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231719, d233533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231729 q = 0) : d233543 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231729, d233543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231729, d233543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231730 q = 0) : d233544 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231730, d233544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231730, d233544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d231731 q = 0) : d233545 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231731, d233545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231731, d233545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro23064 (p : Pattern) (selected : d231733 p = 0) : d233547 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231410 q = 0) : d233289 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231410, d233289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23005 q selected
    | true =>
      simp only [d231410, d233289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231468 q = 0) : d233347 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231468, d233347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231468, d233347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231469 q = 0) : d233348 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231469, d233348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231469, d233348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231470 q = 0) : d233349 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231470, d233349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231470, d233349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231471 q = 0) : d233350 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231471, d233350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231471, d233350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231733 q = 0) : d233547 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231733, d233547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231733, d233547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23065 (p : Pattern) (selected : d231744 p = 0) : d233558 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231739 q = 0) : d233553 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231739, d233553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231739, d233553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23046 q selected
  have h2 (q : Pattern) (selected : d231651 q = 0) : d233488 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231651, d233488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23046 q selected
    | true =>
      simp only [d231651, d233488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231740 q = 0) : d233554 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231740, d233554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231740, d233554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231652 q = 0) : d233489 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231652, d233489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231652, d233489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231741 q = 0) : d233555 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231741, d233555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231741, d233555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231742 q = 0) : d233556 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231742, d233556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231742, d233556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231567 q = 0) : d233423 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231567, d233423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231567, d233423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23017 q selected
  have h8 (q : Pattern) (selected : d231490 q = 0) : d233369 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231490, d233369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23017 q selected
    | true =>
      simp only [d231490, d233369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d231568 q = 0) : d233424 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231568, d233424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231568, d233424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231491 q = 0) : d233370 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231491, d233370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d231491, d233370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d231569 q = 0) : d233425 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231569, d233425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d231569, d233425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d231570 q = 0) : d233426 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231570, d233426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d231570, d233426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d231743 q = 0) : d233557 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d231743, d233557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231743, d233557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d231426 q = 0) : d233305 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231426, d233305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231426, d233305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23000 q selected
  have h15 (q : Pattern) (selected : d231385 q = 0) : d233264 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231385, d233264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23000 q selected
    | true =>
      simp only [d231385, d233264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d231427 q = 0) : d233306 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231427, d233306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d231427, d233306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d231386 q = 0) : d233265 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231386, d233265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d231386, d233265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d231428 q = 0) : d233307 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231428, d233307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d231428, d233307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d231429 q = 0) : d233308 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231429, d233308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d231429, d233308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d231571 q = 0) : d233427 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d231571, d233427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d231571, d233427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d231744 q = 0) : d233558 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231744, d233558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d231744, d233558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro23066 (p : Pattern) (selected : d231750 p = 0) : d233564 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231745 q = 0) : d233559 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231745, d233559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23065 q selected
    | true =>
      simp only [d231745, d233559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23033 q selected
  have h2 (q : Pattern) (selected : d231746 q = 0) : d233560 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231746, d233560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231746, d233560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231747 q = 0) : d233561 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231747, d233561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231747, d233561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231573 q = 0) : d233429 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231573, d233429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23033 q selected
    | true =>
      simp only [d231573, d233429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23008 q selected
  have h5 (q : Pattern) (selected : d231574 q = 0) : d233430 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231574, d233430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231574, d233430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231575 q = 0) : d233431 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231575, d233431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231575, d233431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231748 q = 0) : d233562 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d231748, d233562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231748, d233562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231432 q = 0) : d233311 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231432, d233311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23008 q selected
    | true =>
      simp only [d231432, d233311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d231433 q = 0) : d233312 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231433, d233312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231433, d233312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231434 q = 0) : d233313 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231434, d233313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231434, d233313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d231576 q = 0) : d233432 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d231576, d233432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231576, d233432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d231749 q = 0) : d233563 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d231749, d233563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231749, d233563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d231750 q = 0) : d233564 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d231750, d233564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d231750, d233564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro23067 (p : Pattern) (selected : d231756 p = 0) : d233570 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231751 q = 0) : d233565 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231751, d233565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23066 q selected
    | true =>
      simp only [d231751, d233565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231752 q = 0) : d233566 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231752, d233566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231752, d233566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231579 q = 0) : d233435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231579, d233435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23034 q selected
    | true =>
      simp only [d231579, d233435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231580 q = 0) : d233436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231580, d233436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231580, d233436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231753 q = 0) : d233567 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231753, d233567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231753, d233567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231754 q = 0) : d233568 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231754, d233568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231754, d233568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231755 q = 0) : d233569 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231755, d233569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231755, d233569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d231756 q = 0) : d233570 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231756, d233570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231756, d233570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23068 (p : Pattern) (selected : d231763 p = 0) : d233428 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231758 q = 0) : d233423 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231758, d233423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231758, d233423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23050 q selected
  have h2 (q : Pattern) (selected : d231672 q = 0) : d233369 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231672, d233369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23050 q selected
    | true =>
      simp only [d231672, d233369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231759 q = 0) : d233424 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231759, d233424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231759, d233424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231673 q = 0) : d233370 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231673, d233370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231673, d233370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231760 q = 0) : d233425 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231760, d233425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231760, d233425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231761 q = 0) : d233426 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231761, d233426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231761, d233426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231586 q = 0) : d233305 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231586, d233305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231586, d233305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23021 q selected
  have h8 (q : Pattern) (selected : d231511 q = 0) : d233264 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231511, d233264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23021 q selected
    | true =>
      simp only [d231511, d233264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d231587 q = 0) : d233306 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231587, d233306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231587, d233306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231512 q = 0) : d233265 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231512, d233265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d231512, d233265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d231588 q = 0) : d233307 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231588, d233307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d231588, d233307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d231589 q = 0) : d233308 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231589, d233308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d231589, d233308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d231762 q = 0) : d233427 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d231762, d233427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231762, d233427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d231590 q = 0) : d233309 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d231590, d233309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d231590, d233309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d231763 q = 0) : d233428 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231763, d233428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d231763, d233428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro23069 (p : Pattern) (selected : d231769 p = 0) : d233434 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231764 q = 0) : d233429 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231764, d233429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23068 q selected
    | true =>
      simp only [d231764, d233429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23036 q selected
  have h2 (q : Pattern) (selected : d231765 q = 0) : d233430 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231765, d233430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231765, d233430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231766 q = 0) : d233431 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231766, d233431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231766, d233431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231592 q = 0) : d233311 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231592, d233311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23036 q selected
    | true =>
      simp only [d231592, d233311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231593 q = 0) : d233312 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231593, d233312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231593, d233312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231594 q = 0) : d233313 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231594, d233313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231594, d233313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231767 q = 0) : d233432 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d231767, d233432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231767, d233432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231595 q = 0) : d233314 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d231595, d233314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231595, d233314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d231768 q = 0) : d233433 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d231768, d233433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231768, d233433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231769 q = 0) : d233434 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d231769, d233434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d231769, d233434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro23070 (p : Pattern) (selected : d231775 p = 0) : d233440 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231770 q = 0) : d233435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231770, d233435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23069 q selected
    | true =>
      simp only [d231770, d233435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231771 q = 0) : d233436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231771, d233436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231771, d233436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231598 q = 0) : d233317 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231598, d233317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23037 q selected
    | true =>
      simp only [d231598, d233317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231599 q = 0) : d233318 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231599, d233318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231599, d233318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231772 q = 0) : d233437 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231772, d233437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231772, d233437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231773 q = 0) : d233438 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231773, d233438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231773, d233438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231774 q = 0) : d233439 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231774, d233439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231774, d233439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d231775 q = 0) : d233440 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231775, d233440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231775, d233440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23071 (p : Pattern) (selected : d231781 p = 0) : d233576 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231579 q = 0) : d233435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231579, d233435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23034 q selected
    | true =>
      simp only [d231579, d233435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231580 q = 0) : d233436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231580, d233436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231580, d233436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231778 q = 0) : d233573 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231778, d233573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231778, d233573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231779 q = 0) : d233574 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231779, d233574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231779, d233574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231780 q = 0) : d233575 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231780, d233575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231780, d233575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231781 q = 0) : d233576 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231781, d233576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231781, d233576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23072 (p : Pattern) (selected : d231787 p = 0) : d233582 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231757 q = 0) : d233571 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231757, d233571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23067 q selected
    | true =>
      simp only [d231757, d233571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23035 q selected
  have h2 (q : Pattern) (selected : d231776 q = 0) : d233441 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231776, d233441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23070 q selected
    | true =>
      simp only [d231776, d233441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23038 q selected
  have h3 (q : Pattern) (selected : d231777 q = 0) : d233572 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231777, d233572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231777, d233572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231782 q = 0) : d233577 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231782, d233577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23071 q selected
    | true =>
      simp only [d231782, d233577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231783 q = 0) : d233578 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231783, d233578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231783, d233578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231784 q = 0) : d233579 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231784, d233579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231784, d233579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231785 q = 0) : d233580 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231785, d233580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231785, d233580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231786 q = 0) : d233581 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231786, d233581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231786, d233581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d231787 q = 0) : d233582 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231787, d233582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231787, d233582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro23073 (p : Pattern) (selected : d231793 p = 0) : d233588 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231444 q = 0) : d233323 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231444, d233323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23010 q selected
    | true =>
      simp only [d231444, d233323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231789 q = 0) : d233584 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231789, d233584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231789, d233584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231790 q = 0) : d233585 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231790, d233585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231790, d233585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231791 q = 0) : d233586 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231791, d233586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231791, d233586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231792 q = 0) : d233587 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231792, d233587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231792, d233587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231793 q = 0) : d233588 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231793, d233588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231793, d233588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23074 (p : Pattern) (selected : d231799 p = 0) : d233594 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231627 q = 0) : d233464 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231627, d233464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231627, d233464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23042 q selected
  have h2 (q : Pattern) (selected : d231628 q = 0) : d233465 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231628, d233465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231628, d233465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231634 q = 0) : d233471 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231634, d233471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23042 q selected
    | true =>
      simp only [d231634, d233471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23043 q selected
  have h4 (q : Pattern) (selected : d231635 q = 0) : d233472 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231635, d233472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231635, d233472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231636 q = 0) : d233473 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231636, d233473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231636, d233473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231723 q = 0) : d233537 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231723, d233537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23055 q selected
    | true =>
      simp only [d231723, d233537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23061 q selected
  have h7 (q : Pattern) (selected : d231725 q = 0) : d233539 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231725, d233539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23062 q selected
    | true =>
      simp only [d231725, d233539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23014 q selected
  have h8 (q : Pattern) (selected : d231726 q = 0) : d233540 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231726, d233540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231726, d233540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d231727 q = 0) : d233541 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231727, d233541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d231727, d233541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d231728 q = 0) : d233542 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231728, d233542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231728, d233542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d231732 q = 0) : d233546 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231732, d233546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231732, d233546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23063 q selected
  have h12 (q : Pattern) (selected : d231734 q = 0) : d233548 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231734, d233548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231734, d233548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23064 q selected
  have h13 (q : Pattern) (selected : d231735 q = 0) : d233549 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231735, d233549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d231735, d233549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d231736 q = 0) : d233550 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231736, d233550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d231736, d233550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d231737 q = 0) : d233551 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231737, d233551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d231737, d233551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d231738 q = 0) : d233552 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231738, d233552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d231738, d233552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d231788 q = 0) : d233583 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231788, d233583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231788, d233583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23072 q selected
  have h18 (q : Pattern) (selected : d231794 q = 0) : d233589 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231794, d233589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231794, d233589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23073 q selected
  have h19 (q : Pattern) (selected : d231795 q = 0) : d233590 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231795, d233590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d231795, d233590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d231796 q = 0) : d233591 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231796, d233591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d231796, d233591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d231797 q = 0) : d233592 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231797, d233592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d231797, d233592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d231798 q = 0) : d233593 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231798, d233593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d231798, d233593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d231799 q = 0) : d233594 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d231799, d233594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d231799, d233594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro23075 (p : Pattern) (selected : d231805 p = 0) : d233600 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231800 q = 0) : d233595 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d231800, d233595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231800, d233595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23074 q selected
  have h2 (q : Pattern) (selected : d231801 q = 0) : d233596 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d231801, d233596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231801, d233596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231802 q = 0) : d233597 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d231802, d233597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231802, d233597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231803 q = 0) : d233598 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d231803, d233598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231803, d233598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231804 q = 0) : d233599 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d231804, d233599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231804, d233599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231805 q = 0) : d233600 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d231805, d233600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231805, d233600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23076 (p : Pattern) (selected : d231809 p = 0) : d233604 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231657 q = 0) : d233494 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231657, d233494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23047 q selected
    | true =>
      simp only [d231657, d233494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23018 q selected
  have h2 (q : Pattern) (selected : d231658 q = 0) : d233495 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231658, d233495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231658, d233495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231659 q = 0) : d233496 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231659, d233496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231659, d233496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231496 q = 0) : d233375 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231496, d233375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23018 q selected
    | true =>
      simp only [d231496, d233375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23001 q selected
  have h5 (q : Pattern) (selected : d231497 q = 0) : d233376 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231497, d233376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231497, d233376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231498 q = 0) : d233377 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231498, d233377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231498, d233377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231660 q = 0) : d233497 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d231660, d233497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231660, d233497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231807 q = 0) : d233602 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d231807, d233602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231807, d233602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d231808 q = 0) : d233603 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d231808, d233603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231808, d233603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231809 q = 0) : d233604 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d231809, d233604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d231809, d233604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro23077 (p : Pattern) (selected : d231813 p = 0) : d233608 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231496 q = 0) : d233375 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231496, d233375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23018 q selected
    | true =>
      simp only [d231496, d233375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23001 q selected
  have h2 (q : Pattern) (selected : d231497 q = 0) : d233376 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231497, d233376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231497, d233376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231498 q = 0) : d233377 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231498, d233377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231498, d233377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231807 q = 0) : d233602 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d231807, d233602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231807, d233602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231812 q = 0) : d233607 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d231812, d233607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231812, d233607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231813 q = 0) : d233608 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d231813, d233608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231813, d233608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23078 (p : Pattern) (selected : d231819 p = 0) : d233614 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231810 q = 0) : d233605 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231810, d233605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23076 q selected
    | true =>
      simp only [d231810, d233605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231811 q = 0) : d233606 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231811, d233606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231811, d233606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231814 q = 0) : d233609 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231814, d233609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23077 q selected
    | true =>
      simp only [d231814, d233609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231815 q = 0) : d233610 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231815, d233610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231815, d233610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231816 q = 0) : d233611 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231816, d233611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231816, d233611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231817 q = 0) : d233612 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231817, d233612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231817, d233612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231818 q = 0) : d233613 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231818, d233613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231818, d233613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d231819 q = 0) : d233614 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231819, d233614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231819, d233614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23079 (p : Pattern) (selected : d231823 p = 0) : d233618 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231814 q = 0) : d233609 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231814, d233609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23077 q selected
    | true =>
      simp only [d231814, d233609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231815 q = 0) : d233610 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231815, d233610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231815, d233610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231820 q = 0) : d233615 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231820, d233615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231820, d233615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231821 q = 0) : d233616 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231821, d233616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231821, d233616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231822 q = 0) : d233617 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231822, d233617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231822, d233617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231823 q = 0) : d233618 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231823, d233618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231823, d233618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23080 (p : Pattern) (selected : d231829 p = 0) : d233624 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231824 q = 0) : d233619 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231824, d233619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23078 q selected
    | true =>
      simp only [d231824, d233619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23079 q selected
  have h2 (q : Pattern) (selected : d231825 q = 0) : d233620 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231825, d233620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231825, d233620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231826 q = 0) : d233621 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231826, d233621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231826, d233621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231827 q = 0) : d233622 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231827, d233622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231827, d233622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231828 q = 0) : d233623 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231828, d233623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231828, d233623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231829 q = 0) : d233624 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231829, d233624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231829, d233624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23081 (p : Pattern) (selected : d231832 p = 0) : d233627 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231810 q = 0) : d233605 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231810, d233605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23076 q selected
    | true =>
      simp only [d231810, d233605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231811 q = 0) : d233606 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231811, d233606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231811, d233606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231814 q = 0) : d233609 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231814, d233609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23077 q selected
    | true =>
      simp only [d231814, d233609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231815 q = 0) : d233610 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231815, d233610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231815, d233610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231816 q = 0) : d233611 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231816, d233611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231816, d233611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231817 q = 0) : d233612 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231817, d233612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231817, d233612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231818 q = 0) : d233613 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231818, d233613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231818, d233613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d231832 q = 0) : d233627 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231832, d233627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231832, d233627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23082 (p : Pattern) (selected : d231833 p = 0) : d233628 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231814 q = 0) : d233609 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231814, d233609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23077 q selected
    | true =>
      simp only [d231814, d233609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231815 q = 0) : d233610 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231815, d233610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231815, d233610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231820 q = 0) : d233615 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231820, d233615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231820, d233615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231821 q = 0) : d233616 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231821, d233616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231821, d233616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231822 q = 0) : d233617 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231822, d233617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231822, d233617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231833 q = 0) : d233628 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231833, d233628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231833, d233628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23083 (p : Pattern) (selected : d231839 p = 0) : d233634 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231824 q = 0) : d233619 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231824, d233619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23078 q selected
    | true =>
      simp only [d231824, d233619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23079 q selected
  have h2 (q : Pattern) (selected : d231825 q = 0) : d233620 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231825, d233620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231825, d233620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231826 q = 0) : d233621 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231826, d233621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231826, d233621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231827 q = 0) : d233622 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231827, d233622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231827, d233622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231828 q = 0) : d233623 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231828, d233623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231828, d233623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231834 q = 0) : d233629 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231834, d233629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23081 q selected
    | true =>
      simp only [d231834, d233629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23082 q selected
  have h7 (q : Pattern) (selected : d231835 q = 0) : d233630 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231835, d233630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231835, d233630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231836 q = 0) : d233631 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231836, d233631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231836, d233631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d231837 q = 0) : d233632 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231837, d233632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231837, d233632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231838 q = 0) : d233633 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231838, d233633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231838, d233633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d231839 q = 0) : d233634 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231839, d233634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231839, d233634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro23084 (p : Pattern) (selected : d231844 p = 0) : d233639 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231810 q = 0) : d233605 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231810, d233605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23076 q selected
    | true =>
      simp only [d231810, d233605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231811 q = 0) : d233606 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231811, d233606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231811, d233606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231814 q = 0) : d233609 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231814, d233609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23077 q selected
    | true =>
      simp only [d231814, d233609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231815 q = 0) : d233610 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231815, d233610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231815, d233610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231816 q = 0) : d233611 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231816, d233611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231816, d233611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231817 q = 0) : d233612 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231817, d233612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231817, d233612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231843 q = 0) : d233638 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231843, d233638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231843, d233638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231844 q = 0) : d233639 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231844, d233639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231844, d233639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23085 (p : Pattern) (selected : d231846 p = 0) : d233641 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231814 q = 0) : d233609 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231814, d233609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23077 q selected
    | true =>
      simp only [d231814, d233609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231815 q = 0) : d233610 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231815, d233610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231815, d233610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231820 q = 0) : d233615 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231820, d233615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231820, d233615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231821 q = 0) : d233616 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231821, d233616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231821, d233616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231845 q = 0) : d233640 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231845, d233640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231845, d233640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231846 q = 0) : d233641 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231846, d233641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231846, d233641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23086 (p : Pattern) (selected : d231853 p = 0) : d233648 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231810 q = 0) : d233605 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231810, d233605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23076 q selected
    | true =>
      simp only [d231810, d233605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231811 q = 0) : d233606 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231811, d233606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231811, d233606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231814 q = 0) : d233609 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231814, d233609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23077 q selected
    | true =>
      simp only [d231814, d233609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231815 q = 0) : d233610 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231815, d233610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231815, d233610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231816 q = 0) : d233611 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231816, d233611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231816, d233611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231851 q = 0) : d233646 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231851, d233646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231851, d233646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231852 q = 0) : d233647 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231852, d233647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231852, d233647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d231853 q = 0) : d233648 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231853, d233648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231853, d233648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23087 (p : Pattern) (selected : d231856 p = 0) : d233651 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231814 q = 0) : d233609 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231814, d233609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23077 q selected
    | true =>
      simp only [d231814, d233609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231815 q = 0) : d233610 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231815, d233610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231815, d233610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231820 q = 0) : d233615 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231820, d233615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231820, d233615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231854 q = 0) : d233649 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231854, d233649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231854, d233649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231855 q = 0) : d233650 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231855, d233650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231855, d233650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231856 q = 0) : d233651 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231856, d233651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231856, d233651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23088 (p : Pattern) (selected : d231861 p = 0) : d233656 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d531 q = 0) : d52278 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d52278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro275 q selected
    | true =>
      simp only [d531, d52278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d532 q = 0) : d52279 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d52279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d532, d52279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231860 q = 0) : d233655 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d231860, d233655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231860, d233655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d313 q = 0) : d52112 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d52112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro234 q selected
    | true =>
      simp only [d313, d52112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d314 q = 0) : d52113 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d52113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d314, d52113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231649 q = 0) : d233486 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d231649, d233486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231649, d233486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231861 q = 0) : d233656 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d231861, d233656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231861, d233656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro23089 (p : Pattern) (selected : d231867 p = 0) : d233662 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231862 q = 0) : d233657 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231862, d233657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23088 q selected
    | true =>
      simp only [d231862, d233657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231863 q = 0) : d233658 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231863, d233658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231863, d233658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231864 q = 0) : d233659 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231864, d233659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231864, d233659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231865 q = 0) : d233660 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231865, d233660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231865, d233660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231651 q = 0) : d233488 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231651, d233488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23046 q selected
    | true =>
      simp only [d231651, d233488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231652 q = 0) : d233489 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231652, d233489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231652, d233489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231653 q = 0) : d233490 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231653, d233490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231653, d233490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231654 q = 0) : d233491 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231654, d233491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231654, d233491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d231866 q = 0) : d233661 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d231866, d233661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231866, d233661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231490 q = 0) : d233369 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231490, d233369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23017 q selected
    | true =>
      simp only [d231490, d233369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d231491 q = 0) : d233370 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231491, d233370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d231491, d233370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d231492 q = 0) : d233371 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231492, d233371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231492, d233371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d231493 q = 0) : d233372 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231493, d233372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d231493, d233372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d231655 q = 0) : d233492 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d231655, d233492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d231655, d233492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d231867 q = 0) : d233662 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231867, d233662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d231867, d233662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro23090 (p : Pattern) (selected : d231873 p = 0) : d233668 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231868 q = 0) : d233663 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231868, d233663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23089 q selected
    | true =>
      simp only [d231868, d233663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23047 q selected
  have h2 (q : Pattern) (selected : d231869 q = 0) : d233664 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231869, d233664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231869, d233664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231870 q = 0) : d233665 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231870, d233665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231870, d233665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231657 q = 0) : d233494 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231657, d233494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23047 q selected
    | true =>
      simp only [d231657, d233494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23018 q selected
  have h5 (q : Pattern) (selected : d231658 q = 0) : d233495 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231658, d233495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231658, d233495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231659 q = 0) : d233496 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231659, d233496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231659, d233496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231871 q = 0) : d233666 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d231871, d233666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231871, d233666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231496 q = 0) : d233375 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231496, d233375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23018 q selected
    | true =>
      simp only [d231496, d233375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23001 q selected
  have h9 (q : Pattern) (selected : d231497 q = 0) : d233376 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231497, d233376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231497, d233376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231498 q = 0) : d233377 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231498, d233377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231498, d233377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d231660 q = 0) : d233497 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d231660, d233497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231660, d233497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d231872 q = 0) : d233667 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d231872, d233667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231872, d233667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d231873 q = 0) : d233668 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d231873, d233668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d231873, d233668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro23091 (p : Pattern) (selected : d231879 p = 0) : d233674 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231874 q = 0) : d233669 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231874, d233669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23090 q selected
    | true =>
      simp only [d231874, d233669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231875 q = 0) : d233670 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231875, d233670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231875, d233670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231810 q = 0) : d233605 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231810, d233605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23076 q selected
    | true =>
      simp only [d231810, d233605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231811 q = 0) : d233606 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231811, d233606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231811, d233606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231876 q = 0) : d233671 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231876, d233671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231876, d233671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231877 q = 0) : d233672 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231877, d233672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231877, d233672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231878 q = 0) : d233673 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231878, d233673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231878, d233673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d231879 q = 0) : d233674 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231879, d233674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231879, d233674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23092 (p : Pattern) (selected : d231882 p = 0) : d233487 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d568 q = 0) : d52112 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d568, d52112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro281 q selected
    | true =>
      simp only [d568, d52112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d569 q = 0) : d52113 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d569, d52113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d569, d52113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231881 q = 0) : d233486 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d231881, d233486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231881, d233486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d344 q = 0) : d51984 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d344, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro239 q selected
    | true =>
      simp only [d344, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d345 q = 0) : d51985 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d345, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d345, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231670 q = 0) : d233367 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d231670, d233367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231670, d233367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231882 q = 0) : d233487 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d231882, d233487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231882, d233487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro23093 (p : Pattern) (selected : d231888 p = 0) : d233493 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231883 q = 0) : d233488 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231883, d233488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23092 q selected
    | true =>
      simp only [d231883, d233488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231884 q = 0) : d233489 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231884, d233489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231884, d233489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231885 q = 0) : d233490 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231885, d233490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231885, d233490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231886 q = 0) : d233491 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231886, d233491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231886, d233491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231672 q = 0) : d233369 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231672, d233369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23050 q selected
    | true =>
      simp only [d231672, d233369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231673 q = 0) : d233370 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231673, d233370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231673, d233370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231674 q = 0) : d233371 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231674, d233371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231674, d233371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231675 q = 0) : d233372 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231675, d233372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231675, d233372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d231887 q = 0) : d233492 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d231887, d233492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231887, d233492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231511 q = 0) : d233264 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231511, d233264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23021 q selected
    | true =>
      simp only [d231511, d233264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d231512 q = 0) : d233265 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231512, d233265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d231512, d233265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d231513 q = 0) : d233266 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231513, d233266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231513, d233266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d231514 q = 0) : d233267 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231514, d233267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d231514, d233267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d231676 q = 0) : d233373 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d231676, d233373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d231676, d233373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d231888 q = 0) : d233493 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231888, d233493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d231888, d233493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro23094 (p : Pattern) (selected : d231895 p = 0) : d233604 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231889 q = 0) : d233494 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231889, d233494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23093 q selected
    | true =>
      simp only [d231889, d233494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23051 q selected
  have h2 (q : Pattern) (selected : d231890 q = 0) : d233495 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231890, d233495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231890, d233495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231891 q = 0) : d233496 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231891, d233496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231891, d233496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231678 q = 0) : d233375 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231678, d233375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23051 q selected
    | true =>
      simp only [d231678, d233375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23022 q selected
  have h5 (q : Pattern) (selected : d231679 q = 0) : d233376 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231679, d233376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231679, d233376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231680 q = 0) : d233377 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231680, d233377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231680, d233377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231892 q = 0) : d233497 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d231892, d233497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231892, d233497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231893 q = 0) : d233602 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d231893, d233602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231893, d233602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d231894 q = 0) : d233603 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d231894, d233603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231894, d233603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231895 q = 0) : d233604 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d231895, d233604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d231895, d233604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro23095 (p : Pattern) (selected : d231899 p = 0) : d233608 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231678 q = 0) : d233375 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231678, d233375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23051 q selected
    | true =>
      simp only [d231678, d233375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23022 q selected
  have h2 (q : Pattern) (selected : d231679 q = 0) : d233376 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231679, d233376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231679, d233376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231680 q = 0) : d233377 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231680, d233377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231680, d233377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231893 q = 0) : d233602 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d231893, d233602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231893, d233602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231898 q = 0) : d233607 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d231898, d233607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231898, d233607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231899 q = 0) : d233608 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d231899, d233608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231899, d233608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23096 (p : Pattern) (selected : d231905 p = 0) : d233614 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231896 q = 0) : d233605 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231896, d233605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23094 q selected
    | true =>
      simp only [d231896, d233605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231897 q = 0) : d233606 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231897, d233606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231897, d233606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231900 q = 0) : d233609 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231900, d233609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23095 q selected
    | true =>
      simp only [d231900, d233609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231901 q = 0) : d233610 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231901, d233610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231901, d233610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231902 q = 0) : d233611 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231902, d233611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231902, d233611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231903 q = 0) : d233612 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231903, d233612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231903, d233612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231904 q = 0) : d233613 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231904, d233613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231904, d233613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d231905 q = 0) : d233614 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231905, d233614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231905, d233614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23097 (p : Pattern) (selected : d231909 p = 0) : d233618 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231900 q = 0) : d233609 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231900, d233609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23095 q selected
    | true =>
      simp only [d231900, d233609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231901 q = 0) : d233610 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231901, d233610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231901, d233610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231906 q = 0) : d233615 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231906, d233615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231906, d233615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231907 q = 0) : d233616 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231907, d233616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231907, d233616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231908 q = 0) : d233617 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231908, d233617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231908, d233617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231909 q = 0) : d233618 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231909, d233618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231909, d233618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23098 (p : Pattern) (selected : d231915 p = 0) : d233680 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231810 q = 0) : d233605 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231810, d233605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23076 q selected
    | true =>
      simp only [d231810, d233605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231811 q = 0) : d233606 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231811, d233606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231811, d233606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231912 q = 0) : d233677 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231912, d233677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231912, d233677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231913 q = 0) : d233678 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231913, d233678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231913, d233678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231914 q = 0) : d233679 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231914, d233679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231914, d233679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231915 q = 0) : d233680 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231915, d233680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231915, d233680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23099 (p : Pattern) (selected : d231921 p = 0) : d233686 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231847 q = 0) : d233642 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231847, d233642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23084 q selected
    | true =>
      simp only [d231847, d233642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23085 q selected
  have h2 (q : Pattern) (selected : d231848 q = 0) : d233643 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231848, d233643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231848, d233643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231849 q = 0) : d233644 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231849, d233644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231849, d233644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231850 q = 0) : d233645 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231850, d233645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231850, d233645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231857 q = 0) : d233652 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231857, d233652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23086 q selected
    | true =>
      simp only [d231857, d233652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23087 q selected
  have h6 (q : Pattern) (selected : d231858 q = 0) : d233653 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231858, d233653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231858, d233653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231859 q = 0) : d233654 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231859, d233654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231859, d233654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d231880 q = 0) : d233675 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231880, d233675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23091 q selected
    | true =>
      simp only [d231880, d233675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23078 q selected
  have h9 (q : Pattern) (selected : d231910 q = 0) : d233619 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231910, d233619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23096 q selected
    | true =>
      simp only [d231910, d233619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23097 q selected
  have h10 (q : Pattern) (selected : d231911 q = 0) : d233676 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231911, d233676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d231911, d233676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d231916 q = 0) : d233681 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231916, d233681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23098 q selected
    | true =>
      simp only [d231916, d233681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d231917 q = 0) : d233682 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231917, d233682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d231917, d233682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d231918 q = 0) : d233683 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231918, d233683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d231918, d233683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d231919 q = 0) : d233684 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231919, d233684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231919, d233684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d231920 q = 0) : d233685 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231920, d233685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231920, d233685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d231921 q = 0) : d233686 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231921, d233686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231921, d233686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro23100 (p : Pattern) (selected : d231922 p = 0) : d233687 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231810 q = 0) : d233605 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231810, d233605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23076 q selected
    | true =>
      simp only [d231810, d233605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231811 q = 0) : d233606 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231811, d233606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231811, d233606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231814 q = 0) : d233609 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231814, d233609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23077 q selected
    | true =>
      simp only [d231814, d233609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231815 q = 0) : d233610 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231815, d233610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231815, d233610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231816 q = 0) : d233611 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231816, d233611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231816, d233611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231817 q = 0) : d233612 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231817, d233612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231817, d233612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231843 q = 0) : d233638 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231843, d233638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231843, d233638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231922 q = 0) : d233687 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231922, d233687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231922, d233687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23101 (p : Pattern) (selected : d231923 p = 0) : d233688 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231814 q = 0) : d233609 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231814, d233609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23077 q selected
    | true =>
      simp only [d231814, d233609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231815 q = 0) : d233610 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231815, d233610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231815, d233610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231820 q = 0) : d233615 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231820, d233615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231820, d233615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231821 q = 0) : d233616 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231821, d233616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231821, d233616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231845 q = 0) : d233640 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231845, d233640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231845, d233640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231923 q = 0) : d233688 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231923, d233688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231923, d233688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23102 (p : Pattern) (selected : d231928 p = 0) : d233693 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231810 q = 0) : d233605 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231810, d233605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23076 q selected
    | true =>
      simp only [d231810, d233605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231811 q = 0) : d233606 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231811, d233606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231811, d233606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231814 q = 0) : d233609 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231814, d233609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23077 q selected
    | true =>
      simp only [d231814, d233609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231815 q = 0) : d233610 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231815, d233610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231815, d233610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231816 q = 0) : d233611 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231816, d233611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231816, d233611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231851 q = 0) : d233646 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231851, d233646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231851, d233646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231852 q = 0) : d233647 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231852, d233647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231852, d233647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d231928 q = 0) : d233693 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231928, d233693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231928, d233693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23103 (p : Pattern) (selected : d231929 p = 0) : d233694 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231814 q = 0) : d233609 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231814, d233609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23077 q selected
    | true =>
      simp only [d231814, d233609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231815 q = 0) : d233610 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231815, d233610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231815, d233610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231820 q = 0) : d233615 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231820, d233615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231820, d233615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231854 q = 0) : d233649 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231854, d233649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231854, d233649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231855 q = 0) : d233650 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231855, d233650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231855, d233650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231929 q = 0) : d233694 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231929, d233694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231929, d233694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23104 (p : Pattern) (selected : d231933 p = 0) : d233698 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231874 q = 0) : d233669 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231874, d233669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23090 q selected
    | true =>
      simp only [d231874, d233669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231875 q = 0) : d233670 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231875, d233670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231875, d233670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231810 q = 0) : d233605 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231810, d233605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23076 q selected
    | true =>
      simp only [d231810, d233605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231811 q = 0) : d233606 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231811, d233606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231811, d233606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231876 q = 0) : d233671 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231876, d233671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231876, d233671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231877 q = 0) : d233672 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231877, d233672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231877, d233672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231878 q = 0) : d233673 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231878, d233673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231878, d233673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d231933 q = 0) : d233698 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231933, d233698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231933, d233698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23105 (p : Pattern) (selected : d231935 p = 0) : d233627 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231896 q = 0) : d233605 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231896, d233605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23094 q selected
    | true =>
      simp only [d231896, d233605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231897 q = 0) : d233606 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231897, d233606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231897, d233606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231900 q = 0) : d233609 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231900, d233609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23095 q selected
    | true =>
      simp only [d231900, d233609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231901 q = 0) : d233610 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231901, d233610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231901, d233610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231902 q = 0) : d233611 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231902, d233611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231902, d233611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231903 q = 0) : d233612 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231903, d233612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231903, d233612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231904 q = 0) : d233613 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231904, d233613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231904, d233613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d231935 q = 0) : d233627 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231935, d233627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231935, d233627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23106 (p : Pattern) (selected : d231936 p = 0) : d233628 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231900 q = 0) : d233609 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231900, d233609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23095 q selected
    | true =>
      simp only [d231900, d233609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231901 q = 0) : d233610 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231901, d233610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231901, d233610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231906 q = 0) : d233615 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231906, d233615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231906, d233615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231907 q = 0) : d233616 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231907, d233616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231907, d233616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231908 q = 0) : d233617 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231908, d233617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231908, d233617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231936 q = 0) : d233628 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231936, d233628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231936, d233628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23107 (p : Pattern) (selected : d231939 p = 0) : d233701 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231810 q = 0) : d233605 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231810, d233605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23076 q selected
    | true =>
      simp only [d231810, d233605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231811 q = 0) : d233606 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231811, d233606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231811, d233606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231912 q = 0) : d233677 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231912, d233677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231912, d233677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231913 q = 0) : d233678 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231913, d233678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231913, d233678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231914 q = 0) : d233679 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231914, d233679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231914, d233679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231939 q = 0) : d233701 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231939, d233701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231939, d233701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23108 (p : Pattern) (selected : d231945 p = 0) : d233707 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231847 q = 0) : d233642 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231847, d233642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23084 q selected
    | true =>
      simp only [d231847, d233642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23085 q selected
  have h2 (q : Pattern) (selected : d231848 q = 0) : d233643 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231848, d233643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231848, d233643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231849 q = 0) : d233644 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231849, d233644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231849, d233644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231850 q = 0) : d233645 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231850, d233645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231850, d233645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231857 q = 0) : d233652 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231857, d233652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23086 q selected
    | true =>
      simp only [d231857, d233652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23087 q selected
  have h6 (q : Pattern) (selected : d231858 q = 0) : d233653 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231858, d233653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231858, d233653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231859 q = 0) : d233654 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231859, d233654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231859, d233654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d231880 q = 0) : d233675 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231880, d233675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23091 q selected
    | true =>
      simp only [d231880, d233675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23078 q selected
  have h9 (q : Pattern) (selected : d231910 q = 0) : d233619 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231910, d233619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23096 q selected
    | true =>
      simp only [d231910, d233619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23097 q selected
  have h10 (q : Pattern) (selected : d231911 q = 0) : d233676 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231911, d233676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d231911, d233676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d231916 q = 0) : d233681 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231916, d233681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23098 q selected
    | true =>
      simp only [d231916, d233681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d231917 q = 0) : d233682 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231917, d233682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d231917, d233682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d231918 q = 0) : d233683 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231918, d233683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d231918, d233683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d231919 q = 0) : d233684 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231919, d233684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231919, d233684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d231920 q = 0) : d233685 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231920, d233685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231920, d233685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d231924 q = 0) : d233689 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231924, d233689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23100 q selected
    | true =>
      simp only [d231924, d233689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23101 q selected
  have h17 (q : Pattern) (selected : d231925 q = 0) : d233690 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231925, d233690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231925, d233690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d231926 q = 0) : d233691 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231926, d233691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d231926, d233691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d231927 q = 0) : d233692 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231927, d233692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231927, d233692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d231930 q = 0) : d233695 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231930, d233695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23102 q selected
    | true =>
      simp only [d231930, d233695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23103 q selected
  have h21 (q : Pattern) (selected : d231931 q = 0) : d233696 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231931, d233696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231931, d233696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d231932 q = 0) : d233697 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231932, d233697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d231932, d233697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d231934 q = 0) : d233699 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231934, d233699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23104 q selected
    | true =>
      simp only [d231934, d233699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23081 q selected
  have h24 (q : Pattern) (selected : d231937 q = 0) : d233629 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231937, d233629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23105 q selected
    | true =>
      simp only [d231937, d233629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23106 q selected
  have h25 (q : Pattern) (selected : d231938 q = 0) : d233700 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231938, d233700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d231938, d233700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d231940 q = 0) : d233702 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231940, d233702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23107 q selected
    | true =>
      simp only [d231940, d233702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d231941 q = 0) : d233703 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231941, d233703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d231941, d233703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d231942 q = 0) : d233704 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231942, d233704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d231942, d233704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d231943 q = 0) : d233705 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231943, d233705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d231943, d233705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d231944 q = 0) : d233706 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231944, d233706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d231944, d233706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d231945 q = 0) : d233707 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231945, d233707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d231945, d233707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro23109 (p : Pattern) (selected : d231952 p = 0) : d233714 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231824 q = 0) : d233619 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231824, d233619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23078 q selected
    | true =>
      simp only [d231824, d233619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23079 q selected
  have h2 (q : Pattern) (selected : d231825 q = 0) : d233620 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231825, d233620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231825, d233620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231826 q = 0) : d233621 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231826, d233621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231826, d233621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231827 q = 0) : d233622 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231827, d233622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231827, d233622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231828 q = 0) : d233623 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231828, d233623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231828, d233623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231947 q = 0) : d233709 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231947, d233709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23079 q selected
    | true =>
      simp only [d231947, d233709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231948 q = 0) : d233710 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231948, d233710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231948, d233710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231949 q = 0) : d233711 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231949, d233711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231949, d233711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d231950 q = 0) : d233712 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231950, d233712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231950, d233712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231951 q = 0) : d233713 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231951, d233713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231951, d233713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d231952 q = 0) : d233714 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231952, d233714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231952, d233714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro23110 (p : Pattern) (selected : d231958 p = 0) : d233720 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231947 q = 0) : d233709 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231947, d233709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23079 q selected
    | true =>
      simp only [d231947, d233709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231948 q = 0) : d233710 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231948, d233710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231948, d233710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231949 q = 0) : d233711 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231949, d233711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231949, d233711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231950 q = 0) : d233712 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231950, d233712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231950, d233712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231951 q = 0) : d233713 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231951, d233713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231951, d233713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231953 q = 0) : d233715 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231953, d233715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23082 q selected
    | true =>
      simp only [d231953, d233715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231954 q = 0) : d233716 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231954, d233716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231954, d233716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231955 q = 0) : d233717 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231955, d233717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231955, d233717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d231956 q = 0) : d233718 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231956, d233718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231956, d233718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231957 q = 0) : d233719 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231957, d233719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231957, d233719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d231958 q = 0) : d233720 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231958, d233720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231958, d233720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro23111 (p : Pattern) (selected : d231965 p = 0) : d233727 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231934 q = 0) : d233699 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231934, d233699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23104 q selected
    | true =>
      simp only [d231934, d233699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23081 q selected
  have h2 (q : Pattern) (selected : d231937 q = 0) : d233629 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231937, d233629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23105 q selected
    | true =>
      simp only [d231937, d233629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23106 q selected
  have h3 (q : Pattern) (selected : d231938 q = 0) : d233700 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231938, d233700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231938, d233700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231940 q = 0) : d233702 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231940, d233702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23107 q selected
    | true =>
      simp only [d231940, d233702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231941 q = 0) : d233703 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231941, d233703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231941, d233703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231942 q = 0) : d233704 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231942, d233704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231942, d233704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231963 q = 0) : d233725 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231963, d233725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231963, d233725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231964 q = 0) : d233726 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231964, d233726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231964, d233726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d231965 q = 0) : d233727 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231965, d233727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231965, d233727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro23112 (p : Pattern) (selected : d231967 p = 0) : d233729 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231953 q = 0) : d233715 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d231953, d233715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23082 q selected
    | true =>
      simp only [d231953, d233715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231954 q = 0) : d233716 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d231954, d233716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231954, d233716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231955 q = 0) : d233717 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d231955, d233717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231955, d233717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231956 q = 0) : d233718 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d231956, d233718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231956, d233718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231957 q = 0) : d233719 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d231957, d233719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231957, d233719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231967 q = 0) : d233729 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d231967, d233729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231967, d233729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23113 (p : Pattern) (selected : d231978 p = 0) : d233740 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231973 q = 0) : d233735 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231973, d233735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231973, d233735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23088 q selected
  have h2 (q : Pattern) (selected : d231862 q = 0) : d233657 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231862, d233657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23088 q selected
    | true =>
      simp only [d231862, d233657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231974 q = 0) : d233736 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231974, d233736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231974, d233736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231863 q = 0) : d233658 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231863, d233658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231863, d233658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231975 q = 0) : d233737 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231975, d233737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231975, d233737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231976 q = 0) : d233738 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231976, d233738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231976, d233738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231739 q = 0) : d233553 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231739, d233553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231739, d233553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23046 q selected
  have h8 (q : Pattern) (selected : d231651 q = 0) : d233488 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231651, d233488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23046 q selected
    | true =>
      simp only [d231651, d233488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d231740 q = 0) : d233554 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231740, d233554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231740, d233554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231652 q = 0) : d233489 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231652, d233489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d231652, d233489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d231741 q = 0) : d233555 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231741, d233555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d231741, d233555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d231742 q = 0) : d233556 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231742, d233556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d231742, d233556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d231977 q = 0) : d233739 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d231977, d233739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231977, d233739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d231567 q = 0) : d233423 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231567, d233423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231567, d233423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23017 q selected
  have h15 (q : Pattern) (selected : d231490 q = 0) : d233369 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231490, d233369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23017 q selected
    | true =>
      simp only [d231490, d233369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d231568 q = 0) : d233424 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231568, d233424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d231568, d233424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d231491 q = 0) : d233370 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231491, d233370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d231491, d233370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d231569 q = 0) : d233425 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231569, d233425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d231569, d233425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d231570 q = 0) : d233426 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231570, d233426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d231570, d233426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d231743 q = 0) : d233557 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d231743, d233557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d231743, d233557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d231978 q = 0) : d233740 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231978, d233740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d231978, d233740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro23114 (p : Pattern) (selected : d231984 p = 0) : d233746 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231979 q = 0) : d233741 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231979, d233741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23113 q selected
    | true =>
      simp only [d231979, d233741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23065 q selected
  have h2 (q : Pattern) (selected : d231980 q = 0) : d233742 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231980, d233742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231980, d233742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231981 q = 0) : d233743 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231981, d233743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231981, d233743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231745 q = 0) : d233559 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231745, d233559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23065 q selected
    | true =>
      simp only [d231745, d233559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23033 q selected
  have h5 (q : Pattern) (selected : d231746 q = 0) : d233560 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231746, d233560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231746, d233560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231747 q = 0) : d233561 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231747, d233561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231747, d233561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231982 q = 0) : d233744 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d231982, d233744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231982, d233744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231573 q = 0) : d233429 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231573, d233429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23033 q selected
    | true =>
      simp only [d231573, d233429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23008 q selected
  have h9 (q : Pattern) (selected : d231574 q = 0) : d233430 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231574, d233430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231574, d233430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231575 q = 0) : d233431 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231575, d233431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231575, d233431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d231748 q = 0) : d233562 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d231748, d233562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231748, d233562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d231983 q = 0) : d233745 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d231983, d233745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231983, d233745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d231984 q = 0) : d233746 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d231984, d233746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d231984, d233746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro23115 (p : Pattern) (selected : d231989 p = 0) : d233751 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231745 q = 0) : d233559 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231745, d233559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23065 q selected
    | true =>
      simp only [d231745, d233559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23033 q selected
  have h2 (q : Pattern) (selected : d231746 q = 0) : d233560 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231746, d233560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231746, d233560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231747 q = 0) : d233561 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231747, d233561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231747, d233561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231573 q = 0) : d233429 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231573, d233429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23033 q selected
    | true =>
      simp only [d231573, d233429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23008 q selected
  have h5 (q : Pattern) (selected : d231574 q = 0) : d233430 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231574, d233430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231574, d233430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231575 q = 0) : d233431 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231575, d233431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231575, d233431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d231748 q = 0) : d233562 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d231748, d233562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231748, d233562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d231987 q = 0) : d233749 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d231987, d233749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231987, d233749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d231988 q = 0) : d233750 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d231988, d233750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231988, d233750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231989 q = 0) : d233751 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d231989, d233751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d231989, d233751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro23116 (p : Pattern) (selected : d231995 p = 0) : d233757 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231985 q = 0) : d233747 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231985, d233747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23114 q selected
    | true =>
      simp only [d231985, d233747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231986 q = 0) : d233748 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231986, d233748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231986, d233748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231990 q = 0) : d233752 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231990, d233752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23115 q selected
    | true =>
      simp only [d231990, d233752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231991 q = 0) : d233753 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231991, d233753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231991, d233753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d231992 q = 0) : d233754 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d231992, d233754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231992, d233754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231993 q = 0) : d233755 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d231993, d233755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231993, d233755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231994 q = 0) : d233756 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d231994, d233756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231994, d233756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d231995 q = 0) : d233757 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d231995, d233757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231995, d233757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23117 (p : Pattern) (selected : d231997 p = 0) : d233759 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231573 q = 0) : d233429 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231573, d233429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23033 q selected
    | true =>
      simp only [d231573, d233429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23008 q selected
  have h2 (q : Pattern) (selected : d231574 q = 0) : d233430 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231574, d233430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231574, d233430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231575 q = 0) : d233431 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231575, d233431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231575, d233431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231987 q = 0) : d233749 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d231987, d233749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231987, d233749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231996 q = 0) : d233758 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d231996, d233758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d231996, d233758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d231997 q = 0) : d233759 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d231997, d233759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231997, d233759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23118 (p : Pattern) (selected : d232003 p = 0) : d233765 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231990 q = 0) : d233752 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231990, d233752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23115 q selected
    | true =>
      simp only [d231990, d233752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231991 q = 0) : d233753 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231991, d233753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231991, d233753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231998 q = 0) : d233760 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231998, d233760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23117 q selected
    | true =>
      simp only [d231998, d233760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d231999 q = 0) : d233761 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231999, d233761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231999, d233761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232000 q = 0) : d233762 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232000, d233762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232000, d233762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232001 q = 0) : d233763 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232001, d233763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232001, d233763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232002 q = 0) : d233764 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232002, d233764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232002, d233764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232003 q = 0) : d233765 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232003, d233765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232003, d233765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23119 (p : Pattern) (selected : d232010 p = 0) : d233558 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232005 q = 0) : d233553 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232005, d233553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232005, d233553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23092 q selected
  have h2 (q : Pattern) (selected : d231883 q = 0) : d233488 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231883, d233488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23092 q selected
    | true =>
      simp only [d231883, d233488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232006 q = 0) : d233554 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232006, d233554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232006, d233554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231884 q = 0) : d233489 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231884, d233489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231884, d233489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232007 q = 0) : d233555 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232007, d233555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232007, d233555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232008 q = 0) : d233556 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232008, d233556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232008, d233556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d231758 q = 0) : d233423 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231758, d233423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231758, d233423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23050 q selected
  have h8 (q : Pattern) (selected : d231672 q = 0) : d233369 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231672, d233369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23050 q selected
    | true =>
      simp only [d231672, d233369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d231759 q = 0) : d233424 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231759, d233424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d231759, d233424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231673 q = 0) : d233370 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231673, d233370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d231673, d233370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d231760 q = 0) : d233425 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231760, d233425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d231760, d233425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d231761 q = 0) : d233426 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231761, d233426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d231761, d233426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d232009 q = 0) : d233557 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232009, d233557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232009, d233557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d231586 q = 0) : d233305 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231586, d233305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231586, d233305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23021 q selected
  have h15 (q : Pattern) (selected : d231511 q = 0) : d233264 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231511, d233264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23021 q selected
    | true =>
      simp only [d231511, d233264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d231587 q = 0) : d233306 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231587, d233306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d231587, d233306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d231512 q = 0) : d233265 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231512, d233265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d231512, d233265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d231588 q = 0) : d233307 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231588, d233307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d231588, d233307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d231589 q = 0) : d233308 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231589, d233308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d231589, d233308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d231762 q = 0) : d233427 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d231762, d233427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d231762, d233427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d232010 q = 0) : d233558 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232010, d233558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d232010, d233558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro23120 (p : Pattern) (selected : d232017 p = 0) : d233751 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232011 q = 0) : d233559 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232011, d233559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23119 q selected
    | true =>
      simp only [d232011, d233559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23068 q selected
  have h2 (q : Pattern) (selected : d232012 q = 0) : d233560 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232012, d233560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232012, d233560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232013 q = 0) : d233561 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232013, d233561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232013, d233561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231764 q = 0) : d233429 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231764, d233429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23068 q selected
    | true =>
      simp only [d231764, d233429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23036 q selected
  have h5 (q : Pattern) (selected : d231765 q = 0) : d233430 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231765, d233430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231765, d233430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231766 q = 0) : d233431 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231766, d233431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231766, d233431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232014 q = 0) : d233562 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232014, d233562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232014, d233562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232015 q = 0) : d233749 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232015, d233749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232015, d233749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232016 q = 0) : d233750 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232016, d233750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232016, d233750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232017 q = 0) : d233751 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232017, d233751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232017, d233751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro23121 (p : Pattern) (selected : d232021 p = 0) : d233759 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231764 q = 0) : d233429 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d231764, d233429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23068 q selected
    | true =>
      simp only [d231764, d233429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23036 q selected
  have h2 (q : Pattern) (selected : d231765 q = 0) : d233430 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d231765, d233430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231765, d233430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d231766 q = 0) : d233431 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d231766, d233431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231766, d233431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232015 q = 0) : d233749 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232015, d233749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232015, d233749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232020 q = 0) : d233758 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232020, d233758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232020, d233758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232021 q = 0) : d233759 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232021, d233759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232021, d233759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23122 (p : Pattern) (selected : d232027 p = 0) : d233765 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232018 q = 0) : d233752 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232018, d233752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23120 q selected
    | true =>
      simp only [d232018, d233752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232019 q = 0) : d233753 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232019, d233753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232019, d233753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232022 q = 0) : d233760 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232022, d233760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23121 q selected
    | true =>
      simp only [d232022, d233760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232023 q = 0) : d233761 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232023, d233761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232023, d233761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232024 q = 0) : d233762 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232024, d233762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232024, d233762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232025 q = 0) : d233763 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232025, d233763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232025, d233763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232026 q = 0) : d233764 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232026, d233764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232026, d233764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232027 q = 0) : d233765 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232027, d233765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232027, d233765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23123 (p : Pattern) (selected : d232031 p = 0) : d233770 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232022 q = 0) : d233760 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232022, d233760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23121 q selected
    | true =>
      simp only [d232022, d233760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232023 q = 0) : d233761 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232023, d233761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232023, d233761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232028 q = 0) : d233767 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232028, d233767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232028, d233767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232029 q = 0) : d233768 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232029, d233768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232029, d233768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232030 q = 0) : d233769 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232030, d233769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232030, d233769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232031 q = 0) : d233770 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232031, d233770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232031, d233770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23124 (p : Pattern) (selected : d232037 p = 0) : d233776 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231990 q = 0) : d233752 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231990, d233752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23115 q selected
    | true =>
      simp only [d231990, d233752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231991 q = 0) : d233753 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231991, d233753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231991, d233753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232034 q = 0) : d233773 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232034, d233773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232034, d233773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232035 q = 0) : d233774 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232035, d233774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232035, d233774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232036 q = 0) : d233775 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232036, d233775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232036, d233775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232037 q = 0) : d233776 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232037, d233776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232037, d233776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23125 (p : Pattern) (selected : d232043 p = 0) : d233782 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232004 q = 0) : d233766 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232004, d233766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23116 q selected
    | true =>
      simp only [d232004, d233766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23118 q selected
  have h2 (q : Pattern) (selected : d232032 q = 0) : d233771 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232032, d233771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23122 q selected
    | true =>
      simp only [d232032, d233771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23123 q selected
  have h3 (q : Pattern) (selected : d232033 q = 0) : d233772 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232033, d233772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232033, d233772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232038 q = 0) : d233777 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232038, d233777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23124 q selected
    | true =>
      simp only [d232038, d233777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232039 q = 0) : d233778 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232039, d233778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232039, d233778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232040 q = 0) : d233779 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232040, d233779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232040, d233779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232041 q = 0) : d233780 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232041, d233780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232041, d233780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232042 q = 0) : d233781 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232042, d233781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232042, d233781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d232043 q = 0) : d233782 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d232043, d233782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232043, d233782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro23126 (p : Pattern) (selected : d232048 p = 0) : d233770 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231998 q = 0) : d233760 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d231998, d233760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23117 q selected
    | true =>
      simp only [d231998, d233760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231999 q = 0) : d233761 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d231999, d233761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231999, d233761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232045 q = 0) : d233767 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232045, d233767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232045, d233767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232046 q = 0) : d233768 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232046, d233768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232046, d233768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232047 q = 0) : d233769 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232047, d233769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232047, d233769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232048 q = 0) : d233770 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232048, d233770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232048, d233770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23127 (p : Pattern) (selected : d232054 p = 0) : d233789 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232049 q = 0) : d233784 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232049, d233784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23126 q selected
    | true =>
      simp only [d232049, d233784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232050 q = 0) : d233785 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232050, d233785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232050, d233785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232051 q = 0) : d233786 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232051, d233786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232051, d233786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232052 q = 0) : d233787 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232052, d233787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232052, d233787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232053 q = 0) : d233788 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232053, d233788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232053, d233788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232054 q = 0) : d233789 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d232054, d233789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232054, d233789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23128 (p : Pattern) (selected : d232060 p = 0) : d233795 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231830 q = 0) : d233625 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231830, d233625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231830, d233625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23080 q selected
  have h2 (q : Pattern) (selected : d231831 q = 0) : d233626 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231831, d233626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231831, d233626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231840 q = 0) : d233635 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231840, d233635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23080 q selected
    | true =>
      simp only [d231840, d233635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23083 q selected
  have h4 (q : Pattern) (selected : d231841 q = 0) : d233636 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231841, d233636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231841, d233636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231842 q = 0) : d233637 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231842, d233637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231842, d233637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231946 q = 0) : d233708 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231946, d233708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23099 q selected
    | true =>
      simp only [d231946, d233708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23108 q selected
  have h7 (q : Pattern) (selected : d231959 q = 0) : d233721 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231959, d233721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23109 q selected
    | true =>
      simp only [d231959, d233721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23110 q selected
  have h8 (q : Pattern) (selected : d231960 q = 0) : d233722 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231960, d233722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d231960, d233722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d231961 q = 0) : d233723 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231961, d233723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d231961, d233723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d231962 q = 0) : d233724 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231962, d233724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231962, d233724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d231966 q = 0) : d233728 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231966, d233728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231966, d233728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23111 q selected
  have h12 (q : Pattern) (selected : d231968 q = 0) : d233730 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d231968, d233730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231968, d233730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23112 q selected
  have h13 (q : Pattern) (selected : d231969 q = 0) : d233731 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d231969, d233731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d231969, d233731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d231970 q = 0) : d233732 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d231970, d233732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d231970, d233732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d231971 q = 0) : d233733 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d231971, d233733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d231971, d233733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d231972 q = 0) : d233734 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d231972, d233734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d231972, d233734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d232044 q = 0) : d233783 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d232044, d233783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232044, d233783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23125 q selected
  have h18 (q : Pattern) (selected : d232055 q = 0) : d233790 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d232055, d233790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232055, d233790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23127 q selected
  have h19 (q : Pattern) (selected : d232056 q = 0) : d233791 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d232056, d233791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d232056, d233791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d232057 q = 0) : d233792 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d232057, d233792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d232057, d233792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d232058 q = 0) : d233793 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d232058, d233793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d232058, d233793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d232059 q = 0) : d233794 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d232059, d233794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d232059, d233794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d232060 q = 0) : d233795 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d232060, d233795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d232060, d233795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro23129 (p : Pattern) (selected : d232066 p = 0) : d233801 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232061 q = 0) : d233796 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d232061, d233796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232061, d233796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23128 q selected
  have h2 (q : Pattern) (selected : d232062 q = 0) : d233797 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d232062, d233797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232062, d233797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232063 q = 0) : d233798 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d232063, d233798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232063, d233798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232064 q = 0) : d233799 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d232064, d233799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232064, d233799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232065 q = 0) : d233800 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d232065, d233800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232065, d233800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232066 q = 0) : d233801 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d232066, d233801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232066, d233801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23130 (p : Pattern) (selected : d232071 p = 0) : d233806 p = 1 := by
  have h0 (q : Pattern) (selected : d1088 q = 0) : d52669 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1088, d52669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro275 q selected
    | true =>
      simp only [d1088, d52669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro384 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1089 q = 0) : d52670 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1089, d52670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1089, d52670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232069 q = 0) : d233804 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232069, d233804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232069, d233804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d1094 q = 0) : d52675 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1094, d52675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro234 q selected
    | true =>
      simp only [d1094, d52675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro385 q selected
  have h5 (q : Pattern) (selected : d1095 q = 0) : d52676 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1095, d52676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1095, d52676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d232070 q = 0) : d233805 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232070, d233805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232070, d233805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d232071 q = 0) : d233806 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d232071, d233806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232071, d233806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro23131 (p : Pattern) (selected : d232077 p = 0) : d233812 p = 1 := by
  have h0 (q : Pattern) (selected : d1094 q = 0) : d52675 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1094, d52675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro234 q selected
    | true =>
      simp only [d1094, d52675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro385 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1095 q = 0) : d52676 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1095, d52676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1095, d52676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232070 q = 0) : d233805 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232070, d233805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232070, d233805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d1104 q = 0) : d52685 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1104, d52685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro204 q selected
    | true =>
      simp only [d1104, d52685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
  have h5 (q : Pattern) (selected : d1105 q = 0) : d52686 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1105, d52686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1105, d52686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d232076 q = 0) : d233811 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232076, d233811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232076, d233811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d232077 q = 0) : d233812 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d232077, d233812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232077, d233812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro23132 (p : Pattern) (selected : d232083 p = 0) : d233818 p = 1 := by
  have h0 (q : Pattern) (selected : d1104 q = 0) : d52685 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1104, d52685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro204 q selected
    | true =>
      simp only [d1104, d52685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1105 q = 0) : d52686 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1105, d52686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1105, d52686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232076 q = 0) : d233811 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232076, d233811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232076, d233811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d19 q = 0) : d51871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d20 q = 0) : d51872 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d231383 q = 0) : d233262 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d231383, d233262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231383, d233262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d232083 q = 0) : d233818 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d232083, d233818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232083, d233818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro23133 (p : Pattern) (selected : d232089 p = 0) : d233824 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232072 q = 0) : d233807 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232072, d233807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23130 q selected
    | true =>
      simp only [d232072, d233807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232073 q = 0) : d233808 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232073, d233808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232073, d233808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232074 q = 0) : d233809 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232074, d233809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232074, d233809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232075 q = 0) : d233810 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232075, d233810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232075, d233810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232078 q = 0) : d233813 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232078, d233813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23131 q selected
    | true =>
      simp only [d232078, d233813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232079 q = 0) : d233814 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232079, d233814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232079, d233814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232080 q = 0) : d233815 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232080, d233815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232080, d233815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232081 q = 0) : d233816 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232081, d233816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232081, d233816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232082 q = 0) : d233817 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232082, d233817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232082, d233817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232084 q = 0) : d233819 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232084, d233819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23132 q selected
    | true =>
      simp only [d232084, d233819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232085 q = 0) : d233820 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232085, d233820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d232085, d233820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d232086 q = 0) : d233821 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232086, d233821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232086, d233821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d232087 q = 0) : d233822 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232087, d233822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232087, d233822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d232088 q = 0) : d233823 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232088, d233823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232088, d233823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d232089 q = 0) : d233824 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232089, d233824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232089, d233824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro23134 (p : Pattern) (selected : d232091 p = 0) : d233826 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232078 q = 0) : d233813 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232078, d233813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23131 q selected
    | true =>
      simp only [d232078, d233813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232079 q = 0) : d233814 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232079, d233814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232079, d233814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232080 q = 0) : d233815 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232080, d233815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232080, d233815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232081 q = 0) : d233816 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232081, d233816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232081, d233816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232084 q = 0) : d233819 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232084, d233819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23132 q selected
    | true =>
      simp only [d232084, d233819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232085 q = 0) : d233820 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232085, d233820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232085, d233820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232086 q = 0) : d233821 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232086, d233821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232086, d233821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232087 q = 0) : d233822 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232087, d233822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232087, d233822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232088 q = 0) : d233823 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232088, d233823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232088, d233823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232090 q = 0) : d233825 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232090, d233825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232090, d233825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232091 q = 0) : d233826 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232091, d233826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232091, d233826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro23135 (p : Pattern) (selected : d232095 p = 0) : d233830 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232084 q = 0) : d233819 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232084, d233819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23132 q selected
    | true =>
      simp only [d232084, d233819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232085 q = 0) : d233820 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232085, d233820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232085, d233820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232086 q = 0) : d233821 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232086, d233821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232086, d233821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232087 q = 0) : d233822 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232087, d233822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232087, d233822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232090 q = 0) : d233825 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232090, d233825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232090, d233825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232095 q = 0) : d233830 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232095, d233830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232095, d233830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23136 (p : Pattern) (selected : d232102 p = 0) : d233837 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232092 q = 0) : d233827 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232092, d233827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23133 q selected
    | true =>
      simp only [d232092, d233827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23134 q selected
  have h2 (q : Pattern) (selected : d232093 q = 0) : d233828 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232093, d233828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232093, d233828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232094 q = 0) : d233829 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232094, d233829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232094, d233829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232096 q = 0) : d233831 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232096, d233831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23134 q selected
    | true =>
      simp only [d232096, d233831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23135 q selected
  have h5 (q : Pattern) (selected : d232097 q = 0) : d233832 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232097, d233832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232097, d233832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232098 q = 0) : d233833 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232098, d233833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232098, d233833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232099 q = 0) : d233834 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232099, d233834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232099, d233834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232100 q = 0) : d233835 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232100, d233835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232100, d233835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232101 q = 0) : d233836 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232101, d233836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232101, d233836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232102 q = 0) : d233837 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232102, d233837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232102, d233837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro23137 (p : Pattern) (selected : d232106 p = 0) : d233841 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232096 q = 0) : d233831 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232096, d233831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23134 q selected
    | true =>
      simp only [d232096, d233831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23135 q selected
  have h2 (q : Pattern) (selected : d232097 q = 0) : d233832 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232097, d233832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232097, d233832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232098 q = 0) : d233833 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232098, d233833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232098, d233833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232100 q = 0) : d233835 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232100, d233835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232100, d233835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232105 q = 0) : d233840 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232105, d233840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232105, d233840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232106 q = 0) : d233841 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232106, d233841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232106, d233841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23138 (p : Pattern) (selected : d232112 p = 0) : d233847 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232103 q = 0) : d233838 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232103, d233838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23136 q selected
    | true =>
      simp only [d232103, d233838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232104 q = 0) : d233839 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232104, d233839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232104, d233839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232107 q = 0) : d233842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232107, d233842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23137 q selected
    | true =>
      simp only [d232107, d233842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232108 q = 0) : d233843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232108, d233843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232108, d233843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232109 q = 0) : d233844 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232109, d233844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232109, d233844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232110 q = 0) : d233845 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232110, d233845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232110, d233845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232111 q = 0) : d233846 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232111, d233846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232111, d233846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232112 q = 0) : d233847 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232112, d233847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232112, d233847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23139 (p : Pattern) (selected : d232116 p = 0) : d233851 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232107 q = 0) : d233842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232107, d233842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23137 q selected
    | true =>
      simp only [d232107, d233842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232108 q = 0) : d233843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232108, d233843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232108, d233843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232113 q = 0) : d233848 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232113, d233848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232113, d233848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232114 q = 0) : d233849 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232114, d233849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232114, d233849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232115 q = 0) : d233850 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232115, d233850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232115, d233850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232116 q = 0) : d233851 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232116, d233851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232116, d233851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23140 (p : Pattern) (selected : d232122 p = 0) : d233857 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232117 q = 0) : d233852 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232117, d233852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23138 q selected
    | true =>
      simp only [d232117, d233852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23139 q selected
  have h2 (q : Pattern) (selected : d232118 q = 0) : d233853 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232118, d233853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232118, d233853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232119 q = 0) : d233854 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232119, d233854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232119, d233854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232120 q = 0) : d233855 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232120, d233855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232120, d233855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232121 q = 0) : d233856 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232121, d233856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232121, d233856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232122 q = 0) : d233857 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d232122, d233857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232122, d233857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23141 (p : Pattern) (selected : d232125 p = 0) : d233860 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232103 q = 0) : d233838 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232103, d233838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23136 q selected
    | true =>
      simp only [d232103, d233838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232104 q = 0) : d233839 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232104, d233839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232104, d233839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232107 q = 0) : d233842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232107, d233842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23137 q selected
    | true =>
      simp only [d232107, d233842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232108 q = 0) : d233843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232108, d233843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232108, d233843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232109 q = 0) : d233844 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232109, d233844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232109, d233844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232110 q = 0) : d233845 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232110, d233845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232110, d233845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232111 q = 0) : d233846 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232111, d233846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232111, d233846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232125 q = 0) : d233860 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232125, d233860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232125, d233860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23142 (p : Pattern) (selected : d232126 p = 0) : d233861 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232107 q = 0) : d233842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232107, d233842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23137 q selected
    | true =>
      simp only [d232107, d233842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232108 q = 0) : d233843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232108, d233843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232108, d233843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232113 q = 0) : d233848 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232113, d233848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232113, d233848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232114 q = 0) : d233849 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232114, d233849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232114, d233849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232115 q = 0) : d233850 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232115, d233850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232115, d233850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232126 q = 0) : d233861 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232126, d233861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232126, d233861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23143 (p : Pattern) (selected : d232132 p = 0) : d233867 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232117 q = 0) : d233852 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232117, d233852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23138 q selected
    | true =>
      simp only [d232117, d233852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23139 q selected
  have h2 (q : Pattern) (selected : d232118 q = 0) : d233853 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232118, d233853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232118, d233853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232119 q = 0) : d233854 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232119, d233854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232119, d233854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232120 q = 0) : d233855 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232120, d233855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232120, d233855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232121 q = 0) : d233856 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232121, d233856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232121, d233856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232127 q = 0) : d233862 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232127, d233862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23141 q selected
    | true =>
      simp only [d232127, d233862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23142 q selected
  have h7 (q : Pattern) (selected : d232128 q = 0) : d233863 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232128, d233863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232128, d233863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232129 q = 0) : d233864 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232129, d233864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232129, d233864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232130 q = 0) : d233865 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232130, d233865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232130, d233865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232131 q = 0) : d233866 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232131, d233866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232131, d233866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d232132 q = 0) : d233867 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d232132, d233867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232132, d233867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro23144 (p : Pattern) (selected : d232137 p = 0) : d233872 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232103 q = 0) : d233838 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232103, d233838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23136 q selected
    | true =>
      simp only [d232103, d233838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232104 q = 0) : d233839 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232104, d233839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232104, d233839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232107 q = 0) : d233842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232107, d233842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23137 q selected
    | true =>
      simp only [d232107, d233842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232108 q = 0) : d233843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232108, d233843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232108, d233843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232109 q = 0) : d233844 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232109, d233844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232109, d233844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232110 q = 0) : d233845 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232110, d233845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232110, d233845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232136 q = 0) : d233871 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232136, d233871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232136, d233871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232137 q = 0) : d233872 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232137, d233872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232137, d233872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23145 (p : Pattern) (selected : d232139 p = 0) : d233874 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232107 q = 0) : d233842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232107, d233842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23137 q selected
    | true =>
      simp only [d232107, d233842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232108 q = 0) : d233843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232108, d233843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232108, d233843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232113 q = 0) : d233848 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232113, d233848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232113, d233848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232114 q = 0) : d233849 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232114, d233849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232114, d233849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232138 q = 0) : d233873 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232138, d233873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232138, d233873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232139 q = 0) : d233874 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232139, d233874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232139, d233874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23146 (p : Pattern) (selected : d232146 p = 0) : d233881 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232103 q = 0) : d233838 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232103, d233838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23136 q selected
    | true =>
      simp only [d232103, d233838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232104 q = 0) : d233839 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232104, d233839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232104, d233839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232107 q = 0) : d233842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232107, d233842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23137 q selected
    | true =>
      simp only [d232107, d233842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232108 q = 0) : d233843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232108, d233843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232108, d233843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232109 q = 0) : d233844 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232109, d233844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232109, d233844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232144 q = 0) : d233879 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232144, d233879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232144, d233879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232145 q = 0) : d233880 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232145, d233880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232145, d233880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232146 q = 0) : d233881 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232146, d233881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232146, d233881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23147 (p : Pattern) (selected : d232149 p = 0) : d233884 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232107 q = 0) : d233842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232107, d233842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23137 q selected
    | true =>
      simp only [d232107, d233842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232108 q = 0) : d233843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232108, d233843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232108, d233843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232113 q = 0) : d233848 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232113, d233848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232113, d233848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232147 q = 0) : d233882 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232147, d233882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232147, d233882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232148 q = 0) : d233883 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232148, d233883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232148, d233883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232149 q = 0) : d233884 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232149, d233884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232149, d233884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23148 (p : Pattern) (selected : d232154 p = 0) : d233889 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d822 q = 0) : d52499 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d822, d52499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro333 q selected
    | true =>
      simp only [d822, d52499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d823 q = 0) : d52500 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d823, d52500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d823, d52500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232153 q = 0) : d233888 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232153, d233888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232153, d233888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1088 q = 0) : d52669 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1088, d52669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro275 q selected
    | true =>
      simp only [d1088, d52669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro384 q selected
  have h5 (q : Pattern) (selected : d1089 q = 0) : d52670 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1089, d52670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1089, d52670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232069 q = 0) : d233804 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232069, d233804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232069, d233804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232154 q = 0) : d233889 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d232154, d233889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232154, d233889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro23149 (p : Pattern) (selected : d232160 p = 0) : d233895 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232155 q = 0) : d233890 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232155, d233890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23148 q selected
    | true =>
      simp only [d232155, d233890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232156 q = 0) : d233891 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232156, d233891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232156, d233891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232157 q = 0) : d233892 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232157, d233892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232157, d233892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232158 q = 0) : d233893 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232158, d233893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232158, d233893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232072 q = 0) : d233807 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232072, d233807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23130 q selected
    | true =>
      simp only [d232072, d233807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232073 q = 0) : d233808 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232073, d233808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232073, d233808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232074 q = 0) : d233809 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232074, d233809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232074, d233809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232075 q = 0) : d233810 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232075, d233810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232075, d233810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232159 q = 0) : d233894 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232159, d233894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232159, d233894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232078 q = 0) : d233813 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232078, d233813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23131 q selected
    | true =>
      simp only [d232078, d233813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232079 q = 0) : d233814 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232079, d233814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d232079, d233814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d232080 q = 0) : d233815 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232080, d233815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232080, d233815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d232081 q = 0) : d233816 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232081, d233816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232081, d233816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d232082 q = 0) : d233817 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232082, d233817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232082, d233817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d232160 q = 0) : d233895 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232160, d233895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232160, d233895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro23150 (p : Pattern) (selected : d232166 p = 0) : d233901 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232161 q = 0) : d233896 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232161, d233896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23149 q selected
    | true =>
      simp only [d232161, d233896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23133 q selected
  have h2 (q : Pattern) (selected : d232162 q = 0) : d233897 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232162, d233897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232162, d233897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232163 q = 0) : d233898 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232163, d233898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232163, d233898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232092 q = 0) : d233827 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232092, d233827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23133 q selected
    | true =>
      simp only [d232092, d233827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23134 q selected
  have h5 (q : Pattern) (selected : d232093 q = 0) : d233828 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232093, d233828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232093, d233828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232094 q = 0) : d233829 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232094, d233829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232094, d233829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232164 q = 0) : d233899 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232164, d233899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232164, d233899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232096 q = 0) : d233831 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232096, d233831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23134 q selected
    | true =>
      simp only [d232096, d233831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23135 q selected
  have h9 (q : Pattern) (selected : d232097 q = 0) : d233832 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232097, d233832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232097, d233832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232098 q = 0) : d233833 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232098, d233833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232098, d233833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d232099 q = 0) : d233834 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232099, d233834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232099, d233834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d232165 q = 0) : d233900 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232165, d233900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232165, d233900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d232166 q = 0) : d233901 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232166, d233901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232166, d233901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro23151 (p : Pattern) (selected : d232172 p = 0) : d233907 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232167 q = 0) : d233902 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232167, d233902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23150 q selected
    | true =>
      simp only [d232167, d233902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232168 q = 0) : d233903 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232168, d233903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232168, d233903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232103 q = 0) : d233838 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232103, d233838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23136 q selected
    | true =>
      simp only [d232103, d233838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232104 q = 0) : d233839 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232104, d233839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232104, d233839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232169 q = 0) : d233904 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232169, d233904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232169, d233904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232170 q = 0) : d233905 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232170, d233905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232170, d233905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232171 q = 0) : d233906 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232171, d233906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232171, d233906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232172 q = 0) : d233907 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232172, d233907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232172, d233907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23152 (p : Pattern) (selected : d232176 p = 0) : d233806 p = 1 := by
  have h0 (q : Pattern) (selected : d1237 q = 0) : d52669 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1237, d52669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro339 q selected
    | true =>
      simp only [d1237, d52669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro412 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1238 q = 0) : d52670 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1238, d52670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1238, d52670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232174 q = 0) : d233804 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232174, d233804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232174, d233804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d1249 q = 0) : d52675 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1249, d52675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro281 q selected
    | true =>
      simp only [d1249, d52675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro414 q selected
  have h5 (q : Pattern) (selected : d1250 q = 0) : d52676 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1250, d52676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1250, d52676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d232175 q = 0) : d233805 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232175, d233805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232175, d233805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d232176 q = 0) : d233806 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d232176, d233806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232176, d233806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro23153 (p : Pattern) (selected : d232182 p = 0) : d233812 p = 1 := by
  have h0 (q : Pattern) (selected : d1249 q = 0) : d52675 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1249, d52675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro281 q selected
    | true =>
      simp only [d1249, d52675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro414 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1250 q = 0) : d52676 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1250, d52676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1250, d52676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232175 q = 0) : d233805 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232175, d233805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232175, d233805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d1259 q = 0) : d52685 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1259, d52685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro239 q selected
    | true =>
      simp only [d1259, d52685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
  have h5 (q : Pattern) (selected : d1260 q = 0) : d52686 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1260, d52686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1260, d52686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d232181 q = 0) : d233811 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232181, d233811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232181, d233811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d232182 q = 0) : d233812 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d232182, d233812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232182, d233812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro23154 (p : Pattern) (selected : d232188 p = 0) : d233818 p = 1 := by
  have h0 (q : Pattern) (selected : d1259 q = 0) : d52685 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1259, d52685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro239 q selected
    | true =>
      simp only [d1259, d52685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1260 q = 0) : d52686 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1260, d52686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1260, d52686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232181 q = 0) : d233811 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232181, d233811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232181, d233811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d164 q = 0) : d51871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
    | true =>
      simp only [d164, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d165 q = 0) : d51872 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d165, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d165, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d231509 q = 0) : d233262 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d231509, d233262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231509, d233262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d232188 q = 0) : d233818 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d232188, d233818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232188, d233818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro23155 (p : Pattern) (selected : d232194 p = 0) : d233824 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232177 q = 0) : d233807 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232177, d233807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23152 q selected
    | true =>
      simp only [d232177, d233807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232178 q = 0) : d233808 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232178, d233808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232178, d233808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232179 q = 0) : d233809 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232179, d233809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232179, d233809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232180 q = 0) : d233810 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232180, d233810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232180, d233810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232183 q = 0) : d233813 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232183, d233813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23153 q selected
    | true =>
      simp only [d232183, d233813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232184 q = 0) : d233814 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232184, d233814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232184, d233814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232185 q = 0) : d233815 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232185, d233815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232185, d233815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232186 q = 0) : d233816 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232186, d233816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232186, d233816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232187 q = 0) : d233817 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232187, d233817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232187, d233817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232189 q = 0) : d233819 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232189, d233819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23154 q selected
    | true =>
      simp only [d232189, d233819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232190 q = 0) : d233820 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232190, d233820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d232190, d233820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d232191 q = 0) : d233821 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232191, d233821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232191, d233821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d232192 q = 0) : d233822 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232192, d233822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232192, d233822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d232193 q = 0) : d233823 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232193, d233823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232193, d233823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d232194 q = 0) : d233824 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232194, d233824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232194, d233824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro23156 (p : Pattern) (selected : d232196 p = 0) : d233826 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232183 q = 0) : d233813 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232183, d233813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23153 q selected
    | true =>
      simp only [d232183, d233813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232184 q = 0) : d233814 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232184, d233814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232184, d233814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232185 q = 0) : d233815 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232185, d233815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232185, d233815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232186 q = 0) : d233816 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232186, d233816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232186, d233816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232189 q = 0) : d233819 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232189, d233819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23154 q selected
    | true =>
      simp only [d232189, d233819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232190 q = 0) : d233820 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232190, d233820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232190, d233820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232191 q = 0) : d233821 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232191, d233821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232191, d233821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232192 q = 0) : d233822 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232192, d233822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232192, d233822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232193 q = 0) : d233823 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232193, d233823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232193, d233823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232195 q = 0) : d233825 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232195, d233825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232195, d233825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232196 q = 0) : d233826 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232196, d233826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232196, d233826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro23157 (p : Pattern) (selected : d232200 p = 0) : d233830 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232189 q = 0) : d233819 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232189, d233819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23154 q selected
    | true =>
      simp only [d232189, d233819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232190 q = 0) : d233820 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232190, d233820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232190, d233820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232191 q = 0) : d233821 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232191, d233821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232191, d233821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232192 q = 0) : d233822 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232192, d233822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232192, d233822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232195 q = 0) : d233825 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232195, d233825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232195, d233825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232200 q = 0) : d233830 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232200, d233830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232200, d233830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23158 (p : Pattern) (selected : d232207 p = 0) : d233837 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232197 q = 0) : d233827 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232197, d233827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23155 q selected
    | true =>
      simp only [d232197, d233827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23156 q selected
  have h2 (q : Pattern) (selected : d232198 q = 0) : d233828 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232198, d233828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232198, d233828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232199 q = 0) : d233829 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232199, d233829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232199, d233829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232201 q = 0) : d233831 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232201, d233831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23156 q selected
    | true =>
      simp only [d232201, d233831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23157 q selected
  have h5 (q : Pattern) (selected : d232202 q = 0) : d233832 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232202, d233832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232202, d233832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232203 q = 0) : d233833 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232203, d233833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232203, d233833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232204 q = 0) : d233834 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232204, d233834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232204, d233834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232205 q = 0) : d233835 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232205, d233835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232205, d233835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232206 q = 0) : d233836 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232206, d233836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232206, d233836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232207 q = 0) : d233837 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232207, d233837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232207, d233837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro23159 (p : Pattern) (selected : d232211 p = 0) : d233841 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232201 q = 0) : d233831 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232201, d233831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23156 q selected
    | true =>
      simp only [d232201, d233831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23157 q selected
  have h2 (q : Pattern) (selected : d232202 q = 0) : d233832 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232202, d233832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232202, d233832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232203 q = 0) : d233833 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232203, d233833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232203, d233833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232205 q = 0) : d233835 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232205, d233835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232205, d233835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232210 q = 0) : d233840 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232210, d233840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232210, d233840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232211 q = 0) : d233841 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232211, d233841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232211, d233841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23160 (p : Pattern) (selected : d232217 p = 0) : d233847 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232208 q = 0) : d233838 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232208, d233838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23158 q selected
    | true =>
      simp only [d232208, d233838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232209 q = 0) : d233839 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232209, d233839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232209, d233839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232212 q = 0) : d233842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232212, d233842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23159 q selected
    | true =>
      simp only [d232212, d233842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232213 q = 0) : d233843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232213, d233843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232213, d233843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232214 q = 0) : d233844 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232214, d233844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232214, d233844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232215 q = 0) : d233845 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232215, d233845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232215, d233845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232216 q = 0) : d233846 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232216, d233846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232216, d233846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232217 q = 0) : d233847 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232217, d233847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232217, d233847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23161 (p : Pattern) (selected : d232221 p = 0) : d233851 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232212 q = 0) : d233842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232212, d233842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23159 q selected
    | true =>
      simp only [d232212, d233842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232213 q = 0) : d233843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232213, d233843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232213, d233843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232218 q = 0) : d233848 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232218, d233848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232218, d233848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232219 q = 0) : d233849 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232219, d233849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232219, d233849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232220 q = 0) : d233850 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232220, d233850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232220, d233850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232221 q = 0) : d233851 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232221, d233851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232221, d233851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23162 (p : Pattern) (selected : d232225 p = 0) : d233911 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232078 q = 0) : d233813 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232078, d233813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23131 q selected
    | true =>
      simp only [d232078, d233813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232079 q = 0) : d233814 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232079, d233814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232079, d233814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232080 q = 0) : d233815 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232080, d233815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232080, d233815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232081 q = 0) : d233816 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232081, d233816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232081, d233816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232084 q = 0) : d233819 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232084, d233819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23132 q selected
    | true =>
      simp only [d232084, d233819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232085 q = 0) : d233820 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232085, d233820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232085, d233820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232086 q = 0) : d233821 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232086, d233821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232086, d233821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232087 q = 0) : d233822 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232087, d233822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232087, d233822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232088 q = 0) : d233823 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232088, d233823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232088, d233823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d231490 q = 0) : d233369 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231490, d233369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23017 q selected
    | true =>
      simp only [d231490, d233369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d231491 q = 0) : d233370 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231491, d233370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d231491, d233370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d231492 q = 0) : d233371 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231492, d233371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231492, d233371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d231493 q = 0) : d233372 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231493, d233372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d231493, d233372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d232224 q = 0) : d233910 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232224, d233910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d232224, d233910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d232225 q = 0) : d233911 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232225, d233911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232225, d233911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro23163 (p : Pattern) (selected : d232226 p = 0) : d233912 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231490 q = 0) : d233369 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231490, d233369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23017 q selected
    | true =>
      simp only [d231490, d233369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d231491 q = 0) : d233370 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231491, d233370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231491, d233370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231492 q = 0) : d233371 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231492, d233371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231492, d233371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231493 q = 0) : d233372 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231493, d233372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231493, d233372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232224 q = 0) : d233910 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232224, d233910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232224, d233910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232226 q = 0) : d233912 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232226, d233912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232226, d233912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23164 (p : Pattern) (selected : d232232 p = 0) : d233918 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232092 q = 0) : d233827 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232092, d233827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23133 q selected
    | true =>
      simp only [d232092, d233827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23134 q selected
  have h2 (q : Pattern) (selected : d232093 q = 0) : d233828 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232093, d233828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232093, d233828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232094 q = 0) : d233829 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232094, d233829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232094, d233829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232096 q = 0) : d233831 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232096, d233831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23134 q selected
    | true =>
      simp only [d232096, d233831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23135 q selected
  have h5 (q : Pattern) (selected : d232097 q = 0) : d233832 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232097, d233832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232097, d233832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232098 q = 0) : d233833 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232098, d233833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232098, d233833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232099 q = 0) : d233834 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232099, d233834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232099, d233834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232227 q = 0) : d233913 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232227, d233913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23162 q selected
    | true =>
      simp only [d232227, d233913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23163 q selected
  have h9 (q : Pattern) (selected : d232228 q = 0) : d233914 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232228, d233914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232228, d233914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232229 q = 0) : d233915 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232229, d233915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232229, d233915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d232230 q = 0) : d233916 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232230, d233916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d232230, d233916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d232231 q = 0) : d233917 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232231, d233917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232231, d233917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d232232 q = 0) : d233918 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232232, d233918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232232, d233918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro23165 (p : Pattern) (selected : d232238 p = 0) : d233924 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232233 q = 0) : d233919 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232233, d233919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23164 q selected
    | true =>
      simp only [d232233, d233919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232234 q = 0) : d233920 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232234, d233920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232234, d233920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232235 q = 0) : d233921 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232235, d233921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232235, d233921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232236 q = 0) : d233922 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232236, d233922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232236, d233922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232237 q = 0) : d233923 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232237, d233923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232237, d233923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232238 q = 0) : d233924 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232238, d233924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232238, d233924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23166 (p : Pattern) (selected : d232244 p = 0) : d233930 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232140 q = 0) : d233875 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232140, d233875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23144 q selected
    | true =>
      simp only [d232140, d233875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23145 q selected
  have h2 (q : Pattern) (selected : d232141 q = 0) : d233876 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232141, d233876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232141, d233876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232142 q = 0) : d233877 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232142, d233877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232142, d233877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232143 q = 0) : d233878 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232143, d233878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232143, d233878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232150 q = 0) : d233885 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232150, d233885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23146 q selected
    | true =>
      simp only [d232150, d233885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23147 q selected
  have h6 (q : Pattern) (selected : d232151 q = 0) : d233886 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232151, d233886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232151, d233886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232152 q = 0) : d233887 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232152, d233887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232152, d233887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232173 q = 0) : d233908 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232173, d233908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23151 q selected
    | true =>
      simp only [d232173, d233908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23138 q selected
  have h9 (q : Pattern) (selected : d232222 q = 0) : d233852 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232222, d233852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23160 q selected
    | true =>
      simp only [d232222, d233852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23161 q selected
  have h10 (q : Pattern) (selected : d232223 q = 0) : d233909 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232223, d233909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232223, d233909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d232239 q = 0) : d233925 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232239, d233925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23165 q selected
    | true =>
      simp only [d232239, d233925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d232240 q = 0) : d233926 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232240, d233926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d232240, d233926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d232241 q = 0) : d233927 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232241, d233927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d232241, d233927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d232242 q = 0) : d233928 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232242, d233928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232242, d233928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d232243 q = 0) : d233929 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232243, d233929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232243, d233929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d232244 q = 0) : d233930 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d232244, d233930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232244, d233930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro23167 (p : Pattern) (selected : d232245 p = 0) : d233931 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232103 q = 0) : d233838 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232103, d233838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23136 q selected
    | true =>
      simp only [d232103, d233838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232104 q = 0) : d233839 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232104, d233839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232104, d233839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232107 q = 0) : d233842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232107, d233842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23137 q selected
    | true =>
      simp only [d232107, d233842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232108 q = 0) : d233843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232108, d233843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232108, d233843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232109 q = 0) : d233844 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232109, d233844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232109, d233844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232110 q = 0) : d233845 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232110, d233845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232110, d233845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232136 q = 0) : d233871 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232136, d233871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232136, d233871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232245 q = 0) : d233931 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232245, d233931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232245, d233931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23168 (p : Pattern) (selected : d232246 p = 0) : d233932 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232107 q = 0) : d233842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232107, d233842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23137 q selected
    | true =>
      simp only [d232107, d233842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232108 q = 0) : d233843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232108, d233843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232108, d233843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232113 q = 0) : d233848 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232113, d233848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232113, d233848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232114 q = 0) : d233849 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232114, d233849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232114, d233849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232138 q = 0) : d233873 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232138, d233873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232138, d233873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232246 q = 0) : d233932 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232246, d233932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232246, d233932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23169 (p : Pattern) (selected : d232251 p = 0) : d233937 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232103 q = 0) : d233838 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232103, d233838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23136 q selected
    | true =>
      simp only [d232103, d233838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232104 q = 0) : d233839 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232104, d233839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232104, d233839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232107 q = 0) : d233842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232107, d233842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23137 q selected
    | true =>
      simp only [d232107, d233842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232108 q = 0) : d233843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232108, d233843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232108, d233843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232109 q = 0) : d233844 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232109, d233844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232109, d233844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232144 q = 0) : d233879 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232144, d233879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232144, d233879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232145 q = 0) : d233880 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232145, d233880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232145, d233880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232251 q = 0) : d233937 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232251, d233937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232251, d233937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23170 (p : Pattern) (selected : d232252 p = 0) : d233938 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232107 q = 0) : d233842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232107, d233842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23137 q selected
    | true =>
      simp only [d232107, d233842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232108 q = 0) : d233843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232108, d233843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232108, d233843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232113 q = 0) : d233848 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232113, d233848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232113, d233848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232147 q = 0) : d233882 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232147, d233882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232147, d233882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232148 q = 0) : d233883 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232148, d233883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232148, d233883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232252 q = 0) : d233938 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232252, d233938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232252, d233938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23171 (p : Pattern) (selected : d232256 p = 0) : d233942 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232167 q = 0) : d233902 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232167, d233902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23150 q selected
    | true =>
      simp only [d232167, d233902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232168 q = 0) : d233903 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232168, d233903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232168, d233903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232103 q = 0) : d233838 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232103, d233838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23136 q selected
    | true =>
      simp only [d232103, d233838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232104 q = 0) : d233839 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232104, d233839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232104, d233839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232169 q = 0) : d233904 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232169, d233904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232169, d233904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232170 q = 0) : d233905 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232170, d233905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232170, d233905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232171 q = 0) : d233906 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232171, d233906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232171, d233906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232256 q = 0) : d233942 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232256, d233942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232256, d233942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23172 (p : Pattern) (selected : d232258 p = 0) : d233860 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232208 q = 0) : d233838 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232208, d233838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23158 q selected
    | true =>
      simp only [d232208, d233838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232209 q = 0) : d233839 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232209, d233839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232209, d233839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232212 q = 0) : d233842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232212, d233842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23159 q selected
    | true =>
      simp only [d232212, d233842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232213 q = 0) : d233843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232213, d233843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232213, d233843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232214 q = 0) : d233844 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232214, d233844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232214, d233844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232215 q = 0) : d233845 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232215, d233845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232215, d233845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232216 q = 0) : d233846 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232216, d233846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232216, d233846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232258 q = 0) : d233860 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232258, d233860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232258, d233860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23173 (p : Pattern) (selected : d232259 p = 0) : d233861 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232212 q = 0) : d233842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232212, d233842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23159 q selected
    | true =>
      simp only [d232212, d233842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232213 q = 0) : d233843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232213, d233843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232213, d233843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232218 q = 0) : d233848 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232218, d233848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232218, d233848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232219 q = 0) : d233849 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232219, d233849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232219, d233849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232220 q = 0) : d233850 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232220, d233850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232220, d233850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232259 q = 0) : d233861 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232259, d233861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232259, d233861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23174 (p : Pattern) (selected : d232262 p = 0) : d233945 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232233 q = 0) : d233919 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232233, d233919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23164 q selected
    | true =>
      simp only [d232233, d233919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232234 q = 0) : d233920 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232234, d233920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232234, d233920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232235 q = 0) : d233921 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232235, d233921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232235, d233921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232236 q = 0) : d233922 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232236, d233922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232236, d233922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232237 q = 0) : d233923 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232237, d233923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232237, d233923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232262 q = 0) : d233945 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232262, d233945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232262, d233945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23175 (p : Pattern) (selected : d232268 p = 0) : d233951 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232140 q = 0) : d233875 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232140, d233875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23144 q selected
    | true =>
      simp only [d232140, d233875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23145 q selected
  have h2 (q : Pattern) (selected : d232141 q = 0) : d233876 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232141, d233876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232141, d233876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232142 q = 0) : d233877 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232142, d233877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232142, d233877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232143 q = 0) : d233878 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232143, d233878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232143, d233878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232150 q = 0) : d233885 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232150, d233885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23146 q selected
    | true =>
      simp only [d232150, d233885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23147 q selected
  have h6 (q : Pattern) (selected : d232151 q = 0) : d233886 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232151, d233886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232151, d233886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232152 q = 0) : d233887 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232152, d233887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232152, d233887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232173 q = 0) : d233908 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232173, d233908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23151 q selected
    | true =>
      simp only [d232173, d233908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23138 q selected
  have h9 (q : Pattern) (selected : d232222 q = 0) : d233852 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232222, d233852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23160 q selected
    | true =>
      simp only [d232222, d233852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23161 q selected
  have h10 (q : Pattern) (selected : d232223 q = 0) : d233909 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232223, d233909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232223, d233909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d232239 q = 0) : d233925 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232239, d233925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23165 q selected
    | true =>
      simp only [d232239, d233925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d232240 q = 0) : d233926 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232240, d233926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d232240, d233926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d232241 q = 0) : d233927 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232241, d233927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d232241, d233927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d232242 q = 0) : d233928 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232242, d233928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232242, d233928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d232243 q = 0) : d233929 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232243, d233929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232243, d233929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d232247 q = 0) : d233933 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232247, d233933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23167 q selected
    | true =>
      simp only [d232247, d233933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23168 q selected
  have h17 (q : Pattern) (selected : d232248 q = 0) : d233934 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232248, d233934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232248, d233934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d232249 q = 0) : d233935 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232249, d233935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d232249, d233935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d232250 q = 0) : d233936 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232250, d233936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232250, d233936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d232253 q = 0) : d233939 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232253, d233939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23169 q selected
    | true =>
      simp only [d232253, d233939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23170 q selected
  have h21 (q : Pattern) (selected : d232254 q = 0) : d233940 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232254, d233940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232254, d233940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d232255 q = 0) : d233941 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232255, d233941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d232255, d233941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d232257 q = 0) : d233943 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232257, d233943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23171 q selected
    | true =>
      simp only [d232257, d233943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23141 q selected
  have h24 (q : Pattern) (selected : d232260 q = 0) : d233862 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232260, d233862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23172 q selected
    | true =>
      simp only [d232260, d233862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23173 q selected
  have h25 (q : Pattern) (selected : d232261 q = 0) : d233944 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232261, d233944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d232261, d233944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d232263 q = 0) : d233946 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232263, d233946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23174 q selected
    | true =>
      simp only [d232263, d233946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d232264 q = 0) : d233947 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232264, d233947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d232264, d233947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d232265 q = 0) : d233948 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232265, d233948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d232265, d233948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d232266 q = 0) : d233949 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232266, d233949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d232266, d233949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d232267 q = 0) : d233950 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232267, d233950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d232267, d233950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d232268 q = 0) : d233951 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d232268, d233951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d232268, d233951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro23176 (p : Pattern) (selected : d232275 p = 0) : d233958 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232117 q = 0) : d233852 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232117, d233852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23138 q selected
    | true =>
      simp only [d232117, d233852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23139 q selected
  have h2 (q : Pattern) (selected : d232118 q = 0) : d233853 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232118, d233853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232118, d233853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232119 q = 0) : d233854 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232119, d233854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232119, d233854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232120 q = 0) : d233855 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232120, d233855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232120, d233855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232121 q = 0) : d233856 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232121, d233856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232121, d233856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232270 q = 0) : d233953 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232270, d233953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23139 q selected
    | true =>
      simp only [d232270, d233953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232271 q = 0) : d233954 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232271, d233954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232271, d233954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232272 q = 0) : d233955 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232272, d233955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232272, d233955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232273 q = 0) : d233956 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232273, d233956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232273, d233956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232274 q = 0) : d233957 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232274, d233957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232274, d233957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d232275 q = 0) : d233958 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d232275, d233958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232275, d233958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro23177 (p : Pattern) (selected : d232281 p = 0) : d233964 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232270 q = 0) : d233953 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232270, d233953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23139 q selected
    | true =>
      simp only [d232270, d233953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232271 q = 0) : d233954 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232271, d233954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232271, d233954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232272 q = 0) : d233955 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232272, d233955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232272, d233955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232273 q = 0) : d233956 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232273, d233956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232273, d233956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232274 q = 0) : d233957 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232274, d233957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232274, d233957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232276 q = 0) : d233959 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232276, d233959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23142 q selected
    | true =>
      simp only [d232276, d233959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232277 q = 0) : d233960 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232277, d233960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232277, d233960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232278 q = 0) : d233961 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232278, d233961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232278, d233961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232279 q = 0) : d233962 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232279, d233962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232279, d233962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232280 q = 0) : d233963 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232280, d233963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232280, d233963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d232281 q = 0) : d233964 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d232281, d233964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232281, d233964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro23178 (p : Pattern) (selected : d232288 p = 0) : d233971 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232257 q = 0) : d233943 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232257, d233943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23171 q selected
    | true =>
      simp only [d232257, d233943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23141 q selected
  have h2 (q : Pattern) (selected : d232260 q = 0) : d233862 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232260, d233862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23172 q selected
    | true =>
      simp only [d232260, d233862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23173 q selected
  have h3 (q : Pattern) (selected : d232261 q = 0) : d233944 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232261, d233944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232261, d233944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232263 q = 0) : d233946 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232263, d233946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23174 q selected
    | true =>
      simp only [d232263, d233946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232264 q = 0) : d233947 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232264, d233947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232264, d233947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232265 q = 0) : d233948 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232265, d233948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232265, d233948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232286 q = 0) : d233969 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232286, d233969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232286, d233969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232287 q = 0) : d233970 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232287, d233970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232287, d233970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d232288 q = 0) : d233971 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d232288, d233971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232288, d233971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro23179 (p : Pattern) (selected : d232290 p = 0) : d233973 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232276 q = 0) : d233959 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232276, d233959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23142 q selected
    | true =>
      simp only [d232276, d233959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232277 q = 0) : d233960 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232277, d233960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232277, d233960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232278 q = 0) : d233961 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232278, d233961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232278, d233961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232279 q = 0) : d233962 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232279, d233962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232279, d233962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232280 q = 0) : d233963 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232280, d233963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232280, d233963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232290 q = 0) : d233973 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d232290, d233973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232290, d233973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23180 (p : Pattern) (selected : d232310 p = 0) : d233993 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232296 q = 0) : d233979 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232296, d233979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232296, d233979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23148 q selected
  have h2 (q : Pattern) (selected : d232155 q = 0) : d233890 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232155, d233890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23148 q selected
    | true =>
      simp only [d232155, d233890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232297 q = 0) : d233980 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232297, d233980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232297, d233980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232156 q = 0) : d233891 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232156, d233891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232156, d233891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232298 q = 0) : d233981 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232298, d233981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232298, d233981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232299 q = 0) : d233982 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232299, d233982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232299, d233982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232300 q = 0) : d233983 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232300, d233983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232300, d233983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23130 q selected
  have h8 (q : Pattern) (selected : d232072 q = 0) : d233807 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232072, d233807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23130 q selected
    | true =>
      simp only [d232072, d233807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232301 q = 0) : d233984 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232301, d233984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232301, d233984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232073 q = 0) : d233808 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232073, d233808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232073, d233808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232302 q = 0) : d233985 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232302, d233985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232302, d233985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d232303 q = 0) : d233986 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232303, d233986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d232303, d233986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d232304 q = 0) : d233987 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232304, d233987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232304, d233987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d232305 q = 0) : d233988 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232305, d233988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232305, d233988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23131 q selected
  have h15 (q : Pattern) (selected : d232078 q = 0) : d233813 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232078, d233813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23131 q selected
    | true =>
      simp only [d232078, d233813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d232306 q = 0) : d233989 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232306, d233989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d232306, d233989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d232079 q = 0) : d233814 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232079, d233814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d232079, d233814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d232307 q = 0) : d233990 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232307, d233990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d232307, d233990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d232308 q = 0) : d233991 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232308, d233991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d232308, d233991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d232309 q = 0) : d233992 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232309, d233992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232309, d233992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d232310 q = 0) : d233993 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232310, d233993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d232310, d233993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro23181 (p : Pattern) (selected : d232316 p = 0) : d233999 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232300 q = 0) : d233983 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232300, d233983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232300, d233983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23130 q selected
  have h2 (q : Pattern) (selected : d232072 q = 0) : d233807 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232072, d233807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23130 q selected
    | true =>
      simp only [d232072, d233807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232301 q = 0) : d233984 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232301, d233984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232301, d233984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232073 q = 0) : d233808 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232073, d233808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232073, d233808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232302 q = 0) : d233985 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232302, d233985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232302, d233985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232303 q = 0) : d233986 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232303, d233986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232303, d233986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232305 q = 0) : d233988 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232305, d233988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232305, d233988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23131 q selected
  have h8 (q : Pattern) (selected : d232078 q = 0) : d233813 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232078, d233813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23131 q selected
    | true =>
      simp only [d232078, d233813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232306 q = 0) : d233989 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232306, d233989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232306, d233989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232079 q = 0) : d233814 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232079, d233814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232079, d233814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232307 q = 0) : d233990 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232307, d233990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232307, d233990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d232308 q = 0) : d233991 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232308, d233991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d232308, d233991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d232309 q = 0) : d233992 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232309, d233992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232309, d233992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d232311 q = 0) : d233994 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232311, d233994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232311, d233994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23132 q selected
  have h15 (q : Pattern) (selected : d232084 q = 0) : d233819 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232084, d233819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23132 q selected
    | true =>
      simp only [d232084, d233819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d232312 q = 0) : d233995 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232312, d233995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d232312, d233995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d232085 q = 0) : d233820 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232085, d233820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d232085, d233820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d232313 q = 0) : d233996 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232313, d233996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d232313, d233996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d232314 q = 0) : d233997 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232314, d233997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d232314, d233997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d232315 q = 0) : d233998 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232315, d233998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232315, d233998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d232316 q = 0) : d233999 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232316, d233999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d232316, d233999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro23182 (p : Pattern) (selected : d232321 p = 0) : d234004 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232305 q = 0) : d233988 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232305, d233988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232305, d233988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23131 q selected
  have h2 (q : Pattern) (selected : d232078 q = 0) : d233813 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232078, d233813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23131 q selected
    | true =>
      simp only [d232078, d233813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232306 q = 0) : d233989 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232306, d233989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232306, d233989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232079 q = 0) : d233814 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232079, d233814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232079, d233814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232307 q = 0) : d233990 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232307, d233990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232307, d233990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232308 q = 0) : d233991 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232308, d233991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232308, d233991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232311 q = 0) : d233994 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232311, d233994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232311, d233994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23132 q selected
  have h8 (q : Pattern) (selected : d232084 q = 0) : d233819 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232084, d233819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23132 q selected
    | true =>
      simp only [d232084, d233819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232312 q = 0) : d233995 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232312, d233995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232312, d233995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232085 q = 0) : d233820 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232085, d233820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232085, d233820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232313 q = 0) : d233996 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232313, d233996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232313, d233996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d232314 q = 0) : d233997 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232314, d233997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d232314, d233997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d232315 q = 0) : d233998 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232315, d233998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232315, d233998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d232320 q = 0) : d234003 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232320, d234003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232320, d234003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d232321 q = 0) : d234004 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232321, d234004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d232321, d234004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro23183 (p : Pattern) (selected : d232326 p = 0) : d234009 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232311 q = 0) : d233994 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232311, d233994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232311, d233994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23132 q selected
  have h2 (q : Pattern) (selected : d232084 q = 0) : d233819 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232084, d233819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23132 q selected
    | true =>
      simp only [d232084, d233819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232312 q = 0) : d233995 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232312, d233995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232312, d233995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232085 q = 0) : d233820 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232085, d233820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232085, d233820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232313 q = 0) : d233996 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232313, d233996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232313, d233996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232314 q = 0) : d233997 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232314, d233997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232314, d233997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232320 q = 0) : d234003 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232320, d234003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232320, d234003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232326 q = 0) : d234009 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232326, d234009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232326, d234009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23184 (p : Pattern) (selected : d232332 p = 0) : d234015 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232317 q = 0) : d234000 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232317, d234000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23180 q selected
    | true =>
      simp only [d232317, d234000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23181 q selected
  have h2 (q : Pattern) (selected : d232318 q = 0) : d234001 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232318, d234001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232318, d234001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232319 q = 0) : d234002 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232319, d234002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232319, d234002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232322 q = 0) : d234005 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232322, d234005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23181 q selected
    | true =>
      simp only [d232322, d234005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23182 q selected
  have h5 (q : Pattern) (selected : d232323 q = 0) : d234006 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232323, d234006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232323, d234006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232324 q = 0) : d234007 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232324, d234007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232324, d234007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232325 q = 0) : d234008 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232325, d234008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232325, d234008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232327 q = 0) : d234010 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232327, d234010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23182 q selected
    | true =>
      simp only [d232327, d234010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23183 q selected
  have h9 (q : Pattern) (selected : d232328 q = 0) : d234011 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232328, d234011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232328, d234011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232329 q = 0) : d234012 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232329, d234012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232329, d234012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d232330 q = 0) : d234013 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232330, d234013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232330, d234013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d232331 q = 0) : d234014 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232331, d234014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232331, d234014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d232332 q = 0) : d234015 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232332, d234015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232332, d234015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro23185 (p : Pattern) (selected : d232337 p = 0) : d234020 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232322 q = 0) : d234005 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232322, d234005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23181 q selected
    | true =>
      simp only [d232322, d234005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23182 q selected
  have h2 (q : Pattern) (selected : d232323 q = 0) : d234006 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232323, d234006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232323, d234006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232324 q = 0) : d234007 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232324, d234007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232324, d234007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232327 q = 0) : d234010 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232327, d234010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23182 q selected
    | true =>
      simp only [d232327, d234010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23183 q selected
  have h5 (q : Pattern) (selected : d232328 q = 0) : d234011 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232328, d234011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232328, d234011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232329 q = 0) : d234012 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232329, d234012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232329, d234012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232330 q = 0) : d234013 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232330, d234013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232330, d234013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232335 q = 0) : d234018 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232335, d234018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232335, d234018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232336 q = 0) : d234019 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232336, d234019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232336, d234019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232337 q = 0) : d234020 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232337, d234020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232337, d234020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro23186 (p : Pattern) (selected : d232343 p = 0) : d234026 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232333 q = 0) : d234016 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232333, d234016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23184 q selected
    | true =>
      simp only [d232333, d234016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232334 q = 0) : d234017 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232334, d234017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232334, d234017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232338 q = 0) : d234021 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232338, d234021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23185 q selected
    | true =>
      simp only [d232338, d234021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232339 q = 0) : d234022 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232339, d234022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232339, d234022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232340 q = 0) : d234023 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232340, d234023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232340, d234023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232341 q = 0) : d234024 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232341, d234024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232341, d234024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232342 q = 0) : d234025 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232342, d234025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232342, d234025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232343 q = 0) : d234026 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232343, d234026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232343, d234026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23187 (p : Pattern) (selected : d232345 p = 0) : d234028 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232327 q = 0) : d234010 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232327, d234010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23182 q selected
    | true =>
      simp only [d232327, d234010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23183 q selected
  have h2 (q : Pattern) (selected : d232328 q = 0) : d234011 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232328, d234011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232328, d234011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232329 q = 0) : d234012 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232329, d234012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232329, d234012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232335 q = 0) : d234018 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232335, d234018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232335, d234018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232344 q = 0) : d234027 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232344, d234027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232344, d234027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232345 q = 0) : d234028 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232345, d234028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232345, d234028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23188 (p : Pattern) (selected : d232351 p = 0) : d234034 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232338 q = 0) : d234021 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232338, d234021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23185 q selected
    | true =>
      simp only [d232338, d234021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232339 q = 0) : d234022 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232339, d234022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232339, d234022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232346 q = 0) : d234029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232346, d234029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23187 q selected
    | true =>
      simp only [d232346, d234029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232347 q = 0) : d234030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232347, d234030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232347, d234030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232348 q = 0) : d234031 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232348, d234031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232348, d234031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232349 q = 0) : d234032 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232349, d234032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232349, d234032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232350 q = 0) : d234033 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232350, d234033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232350, d234033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232351 q = 0) : d234034 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232351, d234034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232351, d234034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23189 (p : Pattern) (selected : d232367 p = 0) : d233999 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232353 q = 0) : d233983 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232353, d233983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232353, d233983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23152 q selected
  have h2 (q : Pattern) (selected : d232177 q = 0) : d233807 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232177, d233807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23152 q selected
    | true =>
      simp only [d232177, d233807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232354 q = 0) : d233984 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232354, d233984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232354, d233984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232178 q = 0) : d233808 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232178, d233808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232178, d233808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232355 q = 0) : d233985 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232355, d233985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232355, d233985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232356 q = 0) : d233986 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232356, d233986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232356, d233986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232357 q = 0) : d233988 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232357, d233988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232357, d233988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23153 q selected
  have h8 (q : Pattern) (selected : d232183 q = 0) : d233813 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232183, d233813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23153 q selected
    | true =>
      simp only [d232183, d233813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232358 q = 0) : d233989 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232358, d233989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232358, d233989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232184 q = 0) : d233814 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232184, d233814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232184, d233814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232359 q = 0) : d233990 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232359, d233990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232359, d233990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d232360 q = 0) : d233991 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232360, d233991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d232360, d233991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d232361 q = 0) : d233992 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232361, d233992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232361, d233992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d232362 q = 0) : d233994 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232362, d233994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232362, d233994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23154 q selected
  have h15 (q : Pattern) (selected : d232189 q = 0) : d233819 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232189, d233819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23154 q selected
    | true =>
      simp only [d232189, d233819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d232363 q = 0) : d233995 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232363, d233995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d232363, d233995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d232190 q = 0) : d233820 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232190, d233820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d232190, d233820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d232364 q = 0) : d233996 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232364, d233996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d232364, d233996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d232365 q = 0) : d233997 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232365, d233997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d232365, d233997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d232366 q = 0) : d233998 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232366, d233998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232366, d233998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d232367 q = 0) : d233999 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232367, d233999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d232367, d233999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro23190 (p : Pattern) (selected : d232369 p = 0) : d234004 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232357 q = 0) : d233988 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232357, d233988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232357, d233988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23153 q selected
  have h2 (q : Pattern) (selected : d232183 q = 0) : d233813 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232183, d233813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23153 q selected
    | true =>
      simp only [d232183, d233813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232358 q = 0) : d233989 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232358, d233989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232358, d233989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232184 q = 0) : d233814 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232184, d233814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232184, d233814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232359 q = 0) : d233990 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232359, d233990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232359, d233990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232360 q = 0) : d233991 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232360, d233991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232360, d233991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232362 q = 0) : d233994 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232362, d233994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232362, d233994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23154 q selected
  have h8 (q : Pattern) (selected : d232189 q = 0) : d233819 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232189, d233819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23154 q selected
    | true =>
      simp only [d232189, d233819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232363 q = 0) : d233995 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232363, d233995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232363, d233995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232190 q = 0) : d233820 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232190, d233820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232190, d233820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232364 q = 0) : d233996 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232364, d233996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232364, d233996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d232365 q = 0) : d233997 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232365, d233997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d232365, d233997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d232366 q = 0) : d233998 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232366, d233998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232366, d233998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d232368 q = 0) : d234003 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232368, d234003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232368, d234003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d232369 q = 0) : d234004 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232369, d234004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d232369, d234004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro23191 (p : Pattern) (selected : d232373 p = 0) : d234009 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232362 q = 0) : d233994 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232362, d233994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232362, d233994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23154 q selected
  have h2 (q : Pattern) (selected : d232189 q = 0) : d233819 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232189, d233819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23154 q selected
    | true =>
      simp only [d232189, d233819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232363 q = 0) : d233995 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232363, d233995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232363, d233995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232190 q = 0) : d233820 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232190, d233820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232190, d233820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232364 q = 0) : d233996 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232364, d233996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232364, d233996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232365 q = 0) : d233997 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232365, d233997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232365, d233997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232368 q = 0) : d234003 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232368, d234003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232368, d234003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232373 q = 0) : d234009 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232373, d234009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232373, d234009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23192 (p : Pattern) (selected : d232380 p = 0) : d234020 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232370 q = 0) : d234005 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232370, d234005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23189 q selected
    | true =>
      simp only [d232370, d234005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23190 q selected
  have h2 (q : Pattern) (selected : d232371 q = 0) : d234006 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232371, d234006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232371, d234006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232372 q = 0) : d234007 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232372, d234007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232372, d234007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232374 q = 0) : d234010 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232374, d234010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23190 q selected
    | true =>
      simp only [d232374, d234010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23191 q selected
  have h5 (q : Pattern) (selected : d232375 q = 0) : d234011 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232375, d234011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232375, d234011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232376 q = 0) : d234012 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232376, d234012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232376, d234012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232377 q = 0) : d234013 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232377, d234013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232377, d234013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232378 q = 0) : d234018 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232378, d234018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232378, d234018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232379 q = 0) : d234019 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232379, d234019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232379, d234019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232380 q = 0) : d234020 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232380, d234020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232380, d234020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro23193 (p : Pattern) (selected : d232384 p = 0) : d234028 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232374 q = 0) : d234010 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232374, d234010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23190 q selected
    | true =>
      simp only [d232374, d234010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23191 q selected
  have h2 (q : Pattern) (selected : d232375 q = 0) : d234011 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232375, d234011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232375, d234011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232376 q = 0) : d234012 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232376, d234012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232376, d234012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232378 q = 0) : d234018 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232378, d234018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232378, d234018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232383 q = 0) : d234027 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232383, d234027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232383, d234027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232384 q = 0) : d234028 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232384, d234028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232384, d234028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23194 (p : Pattern) (selected : d232390 p = 0) : d234034 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232381 q = 0) : d234021 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232381, d234021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23192 q selected
    | true =>
      simp only [d232381, d234021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232382 q = 0) : d234022 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232382, d234022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232382, d234022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232385 q = 0) : d234029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232385, d234029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23193 q selected
    | true =>
      simp only [d232385, d234029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232386 q = 0) : d234030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232386, d234030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232386, d234030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232387 q = 0) : d234031 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232387, d234031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232387, d234031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232388 q = 0) : d234032 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232388, d234032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232388, d234032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232389 q = 0) : d234033 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232389, d234033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232389, d234033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232390 q = 0) : d234034 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232390, d234034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232390, d234034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23195 (p : Pattern) (selected : d232394 p = 0) : d234039 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232385 q = 0) : d234029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232385, d234029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23193 q selected
    | true =>
      simp only [d232385, d234029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232386 q = 0) : d234030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232386, d234030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232386, d234030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232391 q = 0) : d234036 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232391, d234036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232391, d234036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232392 q = 0) : d234037 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232392, d234037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232392, d234037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232393 q = 0) : d234038 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232393, d234038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232393, d234038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232394 q = 0) : d234039 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232394, d234039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232394, d234039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23196 (p : Pattern) (selected : d232398 p = 0) : d234043 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232305 q = 0) : d233988 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232305, d233988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232305, d233988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23131 q selected
  have h2 (q : Pattern) (selected : d232078 q = 0) : d233813 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232078, d233813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23131 q selected
    | true =>
      simp only [d232078, d233813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232306 q = 0) : d233989 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232306, d233989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232306, d233989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232079 q = 0) : d233814 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232079, d233814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232079, d233814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232307 q = 0) : d233990 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232307, d233990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232307, d233990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232308 q = 0) : d233991 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232308, d233991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232308, d233991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232311 q = 0) : d233994 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232311, d233994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232311, d233994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23132 q selected
  have h8 (q : Pattern) (selected : d232084 q = 0) : d233819 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232084, d233819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23132 q selected
    | true =>
      simp only [d232084, d233819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232312 q = 0) : d233995 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232312, d233995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232312, d233995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232085 q = 0) : d233820 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232085, d233820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232085, d233820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232313 q = 0) : d233996 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232313, d233996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232313, d233996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d232314 q = 0) : d233997 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232314, d233997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d232314, d233997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d232315 q = 0) : d233998 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232315, d233998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232315, d233998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d231567 q = 0) : d233423 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231567, d233423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231567, d233423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23017 q selected
  have h15 (q : Pattern) (selected : d231490 q = 0) : d233369 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231490, d233369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23017 q selected
    | true =>
      simp only [d231490, d233369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d231568 q = 0) : d233424 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231568, d233424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d231568, d233424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d231491 q = 0) : d233370 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231491, d233370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d231491, d233370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d231569 q = 0) : d233425 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231569, d233425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d231569, d233425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d231570 q = 0) : d233426 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231570, d233426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d231570, d233426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d232397 q = 0) : d234042 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232397, d234042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d232397, d234042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d232398 q = 0) : d234043 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232398, d234043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d232398, d234043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro23197 (p : Pattern) (selected : d232399 p = 0) : d234044 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d231567 q = 0) : d233423 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231567, d233423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d231567, d233423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23017 q selected
  have h2 (q : Pattern) (selected : d231490 q = 0) : d233369 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d231490, d233369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23017 q selected
    | true =>
      simp only [d231490, d233369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d231568 q = 0) : d233424 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231568, d233424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d231568, d233424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d231491 q = 0) : d233370 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d231491, d233370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d231491, d233370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d231569 q = 0) : d233425 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d231569, d233425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d231569, d233425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d231570 q = 0) : d233426 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d231570, d233426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d231570, d233426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232397 q = 0) : d234042 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232397, d234042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232397, d234042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232399 q = 0) : d234044 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232399, d234044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232399, d234044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23198 (p : Pattern) (selected : d232405 p = 0) : d234050 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232322 q = 0) : d234005 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232322, d234005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23181 q selected
    | true =>
      simp only [d232322, d234005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23182 q selected
  have h2 (q : Pattern) (selected : d232323 q = 0) : d234006 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232323, d234006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232323, d234006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232324 q = 0) : d234007 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232324, d234007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232324, d234007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232327 q = 0) : d234010 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232327, d234010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23182 q selected
    | true =>
      simp only [d232327, d234010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23183 q selected
  have h5 (q : Pattern) (selected : d232328 q = 0) : d234011 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232328, d234011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232328, d234011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232329 q = 0) : d234012 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232329, d234012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232329, d234012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232330 q = 0) : d234013 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232330, d234013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232330, d234013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232400 q = 0) : d234045 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232400, d234045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23196 q selected
    | true =>
      simp only [d232400, d234045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23197 q selected
  have h9 (q : Pattern) (selected : d232401 q = 0) : d234046 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232401, d234046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232401, d234046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232402 q = 0) : d234047 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232402, d234047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232402, d234047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d232403 q = 0) : d234048 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232403, d234048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d232403, d234048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d232404 q = 0) : d234049 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232404, d234049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232404, d234049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d232405 q = 0) : d234050 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232405, d234050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232405, d234050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro23199 (p : Pattern) (selected : d232411 p = 0) : d234056 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232406 q = 0) : d234051 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232406, d234051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23198 q selected
    | true =>
      simp only [d232406, d234051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232407 q = 0) : d234052 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232407, d234052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232407, d234052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232408 q = 0) : d234053 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232408, d234053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232408, d234053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232409 q = 0) : d234054 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232409, d234054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232409, d234054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232410 q = 0) : d234055 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232410, d234055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232410, d234055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232411 q = 0) : d234056 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232411, d234056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232411, d234056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23200 (p : Pattern) (selected : d232417 p = 0) : d234062 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232352 q = 0) : d234035 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232352, d234035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23186 q selected
    | true =>
      simp only [d232352, d234035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23188 q selected
  have h2 (q : Pattern) (selected : d232395 q = 0) : d234040 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232395, d234040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23194 q selected
    | true =>
      simp only [d232395, d234040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23195 q selected
  have h3 (q : Pattern) (selected : d232396 q = 0) : d234041 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232396, d234041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232396, d234041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232412 q = 0) : d234057 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232412, d234057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23199 q selected
    | true =>
      simp only [d232412, d234057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232413 q = 0) : d234058 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232413, d234058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232413, d234058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232414 q = 0) : d234059 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232414, d234059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232414, d234059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232415 q = 0) : d234060 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232415, d234060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232415, d234060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232416 q = 0) : d234061 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232416, d234061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232416, d234061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d232417 q = 0) : d234062 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d232417, d234062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232417, d234062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro23201 (p : Pattern) (selected : d232422 p = 0) : d234039 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232346 q = 0) : d234029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232346, d234029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23187 q selected
    | true =>
      simp only [d232346, d234029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232347 q = 0) : d234030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232347, d234030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232347, d234030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232419 q = 0) : d234036 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232419, d234036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232419, d234036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232420 q = 0) : d234037 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232420, d234037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232420, d234037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232421 q = 0) : d234038 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232421, d234038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232421, d234038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232422 q = 0) : d234039 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232422, d234039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232422, d234039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23202 (p : Pattern) (selected : d232428 p = 0) : d234069 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232423 q = 0) : d234064 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232423, d234064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23201 q selected
    | true =>
      simp only [d232423, d234064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232424 q = 0) : d234065 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232424, d234065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232424, d234065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232425 q = 0) : d234066 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232425, d234066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232425, d234066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232426 q = 0) : d234067 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232426, d234067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232426, d234067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232427 q = 0) : d234068 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232427, d234068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232427, d234068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232428 q = 0) : d234069 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d232428, d234069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232428, d234069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23203 (p : Pattern) (selected : d232434 p = 0) : d234075 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232123 q = 0) : d233858 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d232123, d233858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232123, d233858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23140 q selected
  have h2 (q : Pattern) (selected : d232124 q = 0) : d233859 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d232124, d233859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232124, d233859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232133 q = 0) : d233868 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d232133, d233868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23140 q selected
    | true =>
      simp only [d232133, d233868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23143 q selected
  have h4 (q : Pattern) (selected : d232134 q = 0) : d233869 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d232134, d233869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232134, d233869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232135 q = 0) : d233870 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d232135, d233870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232135, d233870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232269 q = 0) : d233952 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d232269, d233952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23166 q selected
    | true =>
      simp only [d232269, d233952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23175 q selected
  have h7 (q : Pattern) (selected : d232282 q = 0) : d233965 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d232282, d233965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23176 q selected
    | true =>
      simp only [d232282, d233965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23177 q selected
  have h8 (q : Pattern) (selected : d232283 q = 0) : d233966 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d232283, d233966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232283, d233966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d232284 q = 0) : d233967 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d232284, d233967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232284, d233967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d232285 q = 0) : d233968 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d232285, d233968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232285, d233968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d232289 q = 0) : d233972 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d232289, d233972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232289, d233972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23178 q selected
  have h12 (q : Pattern) (selected : d232291 q = 0) : d233974 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d232291, d233974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232291, d233974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23179 q selected
  have h13 (q : Pattern) (selected : d232292 q = 0) : d233975 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d232292, d233975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d232292, d233975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d232293 q = 0) : d233976 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d232293, d233976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d232293, d233976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d232294 q = 0) : d233977 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d232294, d233977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d232294, d233977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d232295 q = 0) : d233978 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d232295, d233978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d232295, d233978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d232418 q = 0) : d234063 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d232418, d234063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232418, d234063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23200 q selected
  have h18 (q : Pattern) (selected : d232429 q = 0) : d234070 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d232429, d234070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232429, d234070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23202 q selected
  have h19 (q : Pattern) (selected : d232430 q = 0) : d234071 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d232430, d234071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d232430, d234071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d232431 q = 0) : d234072 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d232431, d234072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d232431, d234072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d232432 q = 0) : d234073 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d232432, d234073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d232432, d234073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d232433 q = 0) : d234074 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d232433, d234074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d232433, d234074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d232434 q = 0) : d234075 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d232434, d234075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d232434, d234075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro23204 (p : Pattern) (selected : d232440 p = 0) : d234081 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232435 q = 0) : d234076 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d232435, d234076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232435, d234076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23203 q selected
  have h2 (q : Pattern) (selected : d232436 q = 0) : d234077 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d232436, d234077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232436, d234077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232437 q = 0) : d234078 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d232437, d234078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232437, d234078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232438 q = 0) : d234079 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d232438, d234079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232438, d234079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232439 q = 0) : d234080 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d232439, d234080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232439, d234080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232440 q = 0) : d234081 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d232440, d234081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232440, d234081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23205 (p : Pattern) (selected : d232446 p = 0) : d234087 p = 1 := by
  have h0 (q : Pattern) (selected : d1527 q = 0) : d52968 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro460 q selected
    | true =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro461 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1528 q = 0) : d52969 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro384 q selected
  have h3 (q : Pattern) (selected : d1529 q = 0) : d52970 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232444 q = 0) : d234085 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232444, d234085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232444, d234085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d1543 q = 0) : d52984 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro463 q selected
    | true =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro464 q selected
  have h6 (q : Pattern) (selected : d1544 q = 0) : d52985 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro385 q selected
  have h7 (q : Pattern) (selected : d1545 q = 0) : d52986 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232445 q = 0) : d234086 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232445, d234086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232445, d234086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d232446 q = 0) : d234087 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d232446, d234087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232446, d234087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro23206 (p : Pattern) (selected : d232452 p = 0) : d234093 p = 1 := by
  have h0 (q : Pattern) (selected : d1543 q = 0) : d52984 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro463 q selected
    | true =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro464 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1544 q = 0) : d52985 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro385 q selected
  have h3 (q : Pattern) (selected : d1545 q = 0) : d52986 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232445 q = 0) : d234086 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232445, d234086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232445, d234086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d1560 q = 0) : d53001 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1560, d53001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro465 q selected
    | true =>
      simp only [d1560, d53001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro467 q selected
  have h6 (q : Pattern) (selected : d1115 q = 0) : d52696 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
  have h7 (q : Pattern) (selected : d1561 q = 0) : d53002 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1561, d53002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1561, d53002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232451 q = 0) : d234092 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232451, d234092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232451, d234092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d232452 q = 0) : d234093 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d232452, d234093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232452, d234093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro23207 (p : Pattern) (selected : d232459 p = 0) : d234100 p = 1 := by
  have h0 (q : Pattern) (selected : d1560 q = 0) : d53001 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1560, d53001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro465 q selected
    | true =>
      simp only [d1560, d53001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro467 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1115 q = 0) : d52696 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
  have h3 (q : Pattern) (selected : d1561 q = 0) : d53002 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1561, d53002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1561, d53002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232451 q = 0) : d234092 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232451, d234092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232451, d234092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d1564 q = 0) : d53005 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro468 q selected
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d1565 q = 0) : d53006 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d232458 q = 0) : d234099 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232458, d234099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232458, d234099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d232459 q = 0) : d234100 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d232459, d234100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232459, d234100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23208 (p : Pattern) (selected : d232465 p = 0) : d234106 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232447 q = 0) : d234088 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232447, d234088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23205 q selected
    | true =>
      simp only [d232447, d234088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232448 q = 0) : d234089 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232448, d234089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232448, d234089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232449 q = 0) : d234090 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232449, d234090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232449, d234090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232450 q = 0) : d234091 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232450, d234091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232450, d234091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232453 q = 0) : d234094 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232453, d234094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23206 q selected
    | true =>
      simp only [d232453, d234094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232454 q = 0) : d234095 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232454, d234095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232454, d234095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232455 q = 0) : d234096 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232455, d234096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232455, d234096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232456 q = 0) : d234097 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232456, d234097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232456, d234097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232457 q = 0) : d234098 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232457, d234098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232457, d234098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232460 q = 0) : d234101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232460, d234101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23207 q selected
    | true =>
      simp only [d232460, d234101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232461 q = 0) : d234102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232461, d234102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d232461, d234102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d232462 q = 0) : d234103 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232462, d234103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232462, d234103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d232463 q = 0) : d234104 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232463, d234104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232463, d234104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d232464 q = 0) : d234105 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232464, d234105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232464, d234105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d232465 q = 0) : d234106 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232465, d234106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232465, d234106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro23209 (p : Pattern) (selected : d232467 p = 0) : d234108 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232453 q = 0) : d234094 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232453, d234094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23206 q selected
    | true =>
      simp only [d232453, d234094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232454 q = 0) : d234095 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232454, d234095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232454, d234095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232455 q = 0) : d234096 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232455, d234096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232455, d234096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232456 q = 0) : d234097 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232456, d234097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232456, d234097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232460 q = 0) : d234101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232460, d234101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23207 q selected
    | true =>
      simp only [d232460, d234101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232461 q = 0) : d234102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232461, d234102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232461, d234102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232462 q = 0) : d234103 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232462, d234103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232462, d234103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232463 q = 0) : d234104 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232463, d234104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232463, d234104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232464 q = 0) : d234105 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232464, d234105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232464, d234105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232466 q = 0) : d234107 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232466, d234107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232466, d234107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232467 q = 0) : d234108 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232467, d234108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232467, d234108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro23210 (p : Pattern) (selected : d232471 p = 0) : d234112 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232460 q = 0) : d234101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232460, d234101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23207 q selected
    | true =>
      simp only [d232460, d234101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232461 q = 0) : d234102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232461, d234102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232461, d234102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232462 q = 0) : d234103 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232462, d234103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232462, d234103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232463 q = 0) : d234104 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232463, d234104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232463, d234104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232466 q = 0) : d234107 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232466, d234107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232466, d234107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232471 q = 0) : d234112 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232471, d234112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232471, d234112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23211 (p : Pattern) (selected : d232478 p = 0) : d234119 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232468 q = 0) : d234109 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232468, d234109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23208 q selected
    | true =>
      simp only [d232468, d234109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23209 q selected
  have h2 (q : Pattern) (selected : d232469 q = 0) : d234110 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232469, d234110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232469, d234110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232470 q = 0) : d234111 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232470, d234111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232470, d234111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232472 q = 0) : d234113 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232472, d234113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23209 q selected
    | true =>
      simp only [d232472, d234113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23210 q selected
  have h5 (q : Pattern) (selected : d232473 q = 0) : d234114 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232473, d234114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232473, d234114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232474 q = 0) : d234115 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232474, d234115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232474, d234115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232475 q = 0) : d234116 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232475, d234116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232475, d234116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232476 q = 0) : d234117 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232476, d234117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232476, d234117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232477 q = 0) : d234118 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232477, d234118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232477, d234118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232478 q = 0) : d234119 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232478, d234119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232478, d234119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro23212 (p : Pattern) (selected : d232482 p = 0) : d234123 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232472 q = 0) : d234113 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232472, d234113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23209 q selected
    | true =>
      simp only [d232472, d234113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23210 q selected
  have h2 (q : Pattern) (selected : d232473 q = 0) : d234114 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232473, d234114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232473, d234114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232474 q = 0) : d234115 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232474, d234115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232474, d234115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232476 q = 0) : d234117 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232476, d234117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232476, d234117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232481 q = 0) : d234122 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232481, d234122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232481, d234122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232482 q = 0) : d234123 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232482, d234123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232482, d234123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23213 (p : Pattern) (selected : d232488 p = 0) : d234129 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232479 q = 0) : d234120 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232479, d234120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23211 q selected
    | true =>
      simp only [d232479, d234120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232480 q = 0) : d234121 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232480, d234121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232480, d234121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232483 q = 0) : d234124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232483, d234124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23212 q selected
    | true =>
      simp only [d232483, d234124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232484 q = 0) : d234125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232484, d234125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232484, d234125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232485 q = 0) : d234126 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232485, d234126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232485, d234126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232486 q = 0) : d234127 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232486, d234127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232486, d234127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232487 q = 0) : d234128 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232487, d234128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232487, d234128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232488 q = 0) : d234129 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232488, d234129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232488, d234129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23214 (p : Pattern) (selected : d232492 p = 0) : d234133 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232483 q = 0) : d234124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232483, d234124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23212 q selected
    | true =>
      simp only [d232483, d234124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232484 q = 0) : d234125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232484, d234125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232484, d234125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232489 q = 0) : d234130 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232489, d234130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232489, d234130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232490 q = 0) : d234131 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232490, d234131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232490, d234131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232491 q = 0) : d234132 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232491, d234132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232491, d234132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232492 q = 0) : d234133 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232492, d234133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232492, d234133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23215 (p : Pattern) (selected : d232498 p = 0) : d234139 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232493 q = 0) : d234134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232493, d234134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23213 q selected
    | true =>
      simp only [d232493, d234134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23214 q selected
  have h2 (q : Pattern) (selected : d232494 q = 0) : d234135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232494, d234135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232494, d234135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232495 q = 0) : d234136 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232495, d234136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232495, d234136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232496 q = 0) : d234137 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232496, d234137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232496, d234137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232497 q = 0) : d234138 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232497, d234138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232497, d234138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232498 q = 0) : d234139 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d232498, d234139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232498, d234139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23216 (p : Pattern) (selected : d232501 p = 0) : d234142 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232479 q = 0) : d234120 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232479, d234120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23211 q selected
    | true =>
      simp only [d232479, d234120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232480 q = 0) : d234121 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232480, d234121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232480, d234121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232483 q = 0) : d234124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232483, d234124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23212 q selected
    | true =>
      simp only [d232483, d234124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232484 q = 0) : d234125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232484, d234125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232484, d234125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232485 q = 0) : d234126 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232485, d234126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232485, d234126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232486 q = 0) : d234127 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232486, d234127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232486, d234127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232487 q = 0) : d234128 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232487, d234128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232487, d234128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232501 q = 0) : d234142 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232501, d234142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232501, d234142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23217 (p : Pattern) (selected : d232502 p = 0) : d234143 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232483 q = 0) : d234124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232483, d234124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23212 q selected
    | true =>
      simp only [d232483, d234124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232484 q = 0) : d234125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232484, d234125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232484, d234125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232489 q = 0) : d234130 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232489, d234130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232489, d234130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232490 q = 0) : d234131 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232490, d234131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232490, d234131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232491 q = 0) : d234132 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232491, d234132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232491, d234132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232502 q = 0) : d234143 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232502, d234143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232502, d234143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23218 (p : Pattern) (selected : d232508 p = 0) : d234149 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232493 q = 0) : d234134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232493, d234134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23213 q selected
    | true =>
      simp only [d232493, d234134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23214 q selected
  have h2 (q : Pattern) (selected : d232494 q = 0) : d234135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232494, d234135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232494, d234135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232495 q = 0) : d234136 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232495, d234136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232495, d234136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232496 q = 0) : d234137 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232496, d234137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232496, d234137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232497 q = 0) : d234138 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232497, d234138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232497, d234138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232503 q = 0) : d234144 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232503, d234144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23216 q selected
    | true =>
      simp only [d232503, d234144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23217 q selected
  have h7 (q : Pattern) (selected : d232504 q = 0) : d234145 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232504, d234145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232504, d234145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232505 q = 0) : d234146 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232505, d234146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232505, d234146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232506 q = 0) : d234147 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232506, d234147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232506, d234147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232507 q = 0) : d234148 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232507, d234148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232507, d234148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d232508 q = 0) : d234149 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d232508, d234149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232508, d234149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro23219 (p : Pattern) (selected : d232513 p = 0) : d234154 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232479 q = 0) : d234120 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232479, d234120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23211 q selected
    | true =>
      simp only [d232479, d234120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232480 q = 0) : d234121 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232480, d234121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232480, d234121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232483 q = 0) : d234124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232483, d234124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23212 q selected
    | true =>
      simp only [d232483, d234124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232484 q = 0) : d234125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232484, d234125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232484, d234125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232485 q = 0) : d234126 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232485, d234126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232485, d234126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232486 q = 0) : d234127 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232486, d234127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232486, d234127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232512 q = 0) : d234153 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232512, d234153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232512, d234153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232513 q = 0) : d234154 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232513, d234154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232513, d234154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23220 (p : Pattern) (selected : d232515 p = 0) : d234156 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232483 q = 0) : d234124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232483, d234124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23212 q selected
    | true =>
      simp only [d232483, d234124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232484 q = 0) : d234125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232484, d234125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232484, d234125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232489 q = 0) : d234130 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232489, d234130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232489, d234130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232490 q = 0) : d234131 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232490, d234131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232490, d234131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232514 q = 0) : d234155 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232514, d234155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232514, d234155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232515 q = 0) : d234156 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232515, d234156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232515, d234156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23221 (p : Pattern) (selected : d232522 p = 0) : d234163 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232479 q = 0) : d234120 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232479, d234120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23211 q selected
    | true =>
      simp only [d232479, d234120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232480 q = 0) : d234121 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232480, d234121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232480, d234121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232483 q = 0) : d234124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232483, d234124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23212 q selected
    | true =>
      simp only [d232483, d234124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232484 q = 0) : d234125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232484, d234125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232484, d234125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232485 q = 0) : d234126 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232485, d234126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232485, d234126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232520 q = 0) : d234161 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232520, d234161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232520, d234161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232521 q = 0) : d234162 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232521, d234162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232521, d234162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232522 q = 0) : d234163 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232522, d234163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232522, d234163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23222 (p : Pattern) (selected : d232525 p = 0) : d234166 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232483 q = 0) : d234124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232483, d234124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23212 q selected
    | true =>
      simp only [d232483, d234124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232484 q = 0) : d234125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232484, d234125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232484, d234125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232489 q = 0) : d234130 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232489, d234130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232489, d234130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232523 q = 0) : d234164 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232523, d234164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232523, d234164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232524 q = 0) : d234165 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232524, d234165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232524, d234165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232525 q = 0) : d234166 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232525, d234166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232525, d234166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23223 (p : Pattern) (selected : d232530 p = 0) : d234171 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1200 q = 0) : d52781 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1200, d52781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro405 q selected
    | true =>
      simp only [d1200, d52781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1201 q = 0) : d52782 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1201, d52782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1201, d52782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232529 q = 0) : d234170 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232529, d234170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232529, d234170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1527 q = 0) : d52968 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro460 q selected
    | true =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro461 q selected
  have h5 (q : Pattern) (selected : d1528 q = 0) : d52969 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro384 q selected
  have h6 (q : Pattern) (selected : d1529 q = 0) : d52970 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232444 q = 0) : d234085 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232444, d234085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232444, d234085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232530 q = 0) : d234171 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d232530, d234171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232530, d234171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23224 (p : Pattern) (selected : d232536 p = 0) : d234177 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232531 q = 0) : d234172 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232531, d234172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23223 q selected
    | true =>
      simp only [d232531, d234172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232532 q = 0) : d234173 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232532, d234173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232532, d234173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232533 q = 0) : d234174 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232533, d234174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232533, d234174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232534 q = 0) : d234175 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232534, d234175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232534, d234175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232447 q = 0) : d234088 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232447, d234088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23205 q selected
    | true =>
      simp only [d232447, d234088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232448 q = 0) : d234089 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232448, d234089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232448, d234089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232449 q = 0) : d234090 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232449, d234090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232449, d234090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232450 q = 0) : d234091 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232450, d234091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232450, d234091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232535 q = 0) : d234176 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232535, d234176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232535, d234176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232453 q = 0) : d234094 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232453, d234094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23206 q selected
    | true =>
      simp only [d232453, d234094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232454 q = 0) : d234095 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232454, d234095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d232454, d234095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d232455 q = 0) : d234096 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232455, d234096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232455, d234096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d232456 q = 0) : d234097 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232456, d234097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232456, d234097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d232457 q = 0) : d234098 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232457, d234098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232457, d234098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d232536 q = 0) : d234177 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232536, d234177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232536, d234177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro23225 (p : Pattern) (selected : d232542 p = 0) : d234183 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232537 q = 0) : d234178 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232537, d234178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23224 q selected
    | true =>
      simp only [d232537, d234178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23208 q selected
  have h2 (q : Pattern) (selected : d232538 q = 0) : d234179 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232538, d234179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232538, d234179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232539 q = 0) : d234180 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232539, d234180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232539, d234180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232468 q = 0) : d234109 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232468, d234109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23208 q selected
    | true =>
      simp only [d232468, d234109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23209 q selected
  have h5 (q : Pattern) (selected : d232469 q = 0) : d234110 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232469, d234110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232469, d234110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232470 q = 0) : d234111 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232470, d234111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232470, d234111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232540 q = 0) : d234181 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232540, d234181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232540, d234181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232472 q = 0) : d234113 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232472, d234113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23209 q selected
    | true =>
      simp only [d232472, d234113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23210 q selected
  have h9 (q : Pattern) (selected : d232473 q = 0) : d234114 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232473, d234114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232473, d234114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232474 q = 0) : d234115 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232474, d234115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232474, d234115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d232475 q = 0) : d234116 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232475, d234116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232475, d234116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d232541 q = 0) : d234182 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232541, d234182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232541, d234182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d232542 q = 0) : d234183 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232542, d234183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232542, d234183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro23226 (p : Pattern) (selected : d232548 p = 0) : d234189 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232543 q = 0) : d234184 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232543, d234184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23225 q selected
    | true =>
      simp only [d232543, d234184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232544 q = 0) : d234185 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232544, d234185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232544, d234185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232479 q = 0) : d234120 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232479, d234120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23211 q selected
    | true =>
      simp only [d232479, d234120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232480 q = 0) : d234121 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232480, d234121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232480, d234121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232545 q = 0) : d234186 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232545, d234186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232545, d234186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232546 q = 0) : d234187 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232546, d234187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232546, d234187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232547 q = 0) : d234188 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232547, d234188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232547, d234188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232548 q = 0) : d234189 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232548, d234189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232548, d234189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23227 (p : Pattern) (selected : d232552 p = 0) : d234087 p = 1 := by
  have h0 (q : Pattern) (selected : d1695 q = 0) : d52968 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1695, d52968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro492 q selected
    | true =>
      simp only [d1695, d52968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro493 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1696 q = 0) : d52969 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1696, d52969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1696, d52969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro412 q selected
  have h3 (q : Pattern) (selected : d1697 q = 0) : d52970 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1697, d52970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1697, d52970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232550 q = 0) : d234085 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232550, d234085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232550, d234085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d1714 q = 0) : d52984 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1714, d52984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro496 q selected
    | true =>
      simp only [d1714, d52984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro497 q selected
  have h6 (q : Pattern) (selected : d1715 q = 0) : d52985 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1715, d52985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1715, d52985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro414 q selected
  have h7 (q : Pattern) (selected : d1716 q = 0) : d52986 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1716, d52986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1716, d52986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232551 q = 0) : d234086 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232551, d234086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232551, d234086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d232552 q = 0) : d234087 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d232552, d234087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232552, d234087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro23228 (p : Pattern) (selected : d232558 p = 0) : d234093 p = 1 := by
  have h0 (q : Pattern) (selected : d1714 q = 0) : d52984 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1714, d52984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro496 q selected
    | true =>
      simp only [d1714, d52984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro497 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1715 q = 0) : d52985 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1715, d52985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1715, d52985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro414 q selected
  have h3 (q : Pattern) (selected : d1716 q = 0) : d52986 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1716, d52986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1716, d52986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232551 q = 0) : d234086 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232551, d234086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232551, d234086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d1731 q = 0) : d53001 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1731, d53001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro498 q selected
    | true =>
      simp only [d1731, d53001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro500 q selected
  have h6 (q : Pattern) (selected : d1270 q = 0) : d52696 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1270, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1270, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
  have h7 (q : Pattern) (selected : d1732 q = 0) : d53002 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1732, d53002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1732, d53002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232557 q = 0) : d234092 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232557, d234092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232557, d234092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d232558 q = 0) : d234093 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d232558, d234093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232558, d234093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro23229 (p : Pattern) (selected : d232565 p = 0) : d234100 p = 1 := by
  have h0 (q : Pattern) (selected : d1731 q = 0) : d53001 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1731, d53001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro498 q selected
    | true =>
      simp only [d1731, d53001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro500 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d1270 q = 0) : d52696 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1270, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1270, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
  have h3 (q : Pattern) (selected : d1732 q = 0) : d53002 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1732, d53002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1732, d53002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232557 q = 0) : d234092 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232557, d234092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232557, d234092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d1735 q = 0) : d53005 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1735, d53005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro501 q selected
    | true =>
      simp only [d1735, d53005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d1736 q = 0) : d53006 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1736, d53006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1736, d53006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d232564 q = 0) : d234099 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232564, d234099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232564, d234099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d232565 q = 0) : d234100 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d232565, d234100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232565, d234100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23230 (p : Pattern) (selected : d232571 p = 0) : d234106 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232553 q = 0) : d234088 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232553, d234088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23227 q selected
    | true =>
      simp only [d232553, d234088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232554 q = 0) : d234089 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232554, d234089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232554, d234089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232555 q = 0) : d234090 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232555, d234090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232555, d234090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232556 q = 0) : d234091 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232556, d234091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232556, d234091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232559 q = 0) : d234094 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232559, d234094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23228 q selected
    | true =>
      simp only [d232559, d234094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232560 q = 0) : d234095 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232560, d234095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232560, d234095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232561 q = 0) : d234096 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232561, d234096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232561, d234096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232562 q = 0) : d234097 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232562, d234097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232562, d234097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232563 q = 0) : d234098 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232563, d234098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232563, d234098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232566 q = 0) : d234101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232566, d234101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23229 q selected
    | true =>
      simp only [d232566, d234101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232567 q = 0) : d234102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232567, d234102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d232567, d234102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d232568 q = 0) : d234103 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232568, d234103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232568, d234103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d232569 q = 0) : d234104 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232569, d234104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232569, d234104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d232570 q = 0) : d234105 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232570, d234105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232570, d234105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d232571 q = 0) : d234106 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232571, d234106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232571, d234106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro23231 (p : Pattern) (selected : d232573 p = 0) : d234108 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232559 q = 0) : d234094 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232559, d234094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23228 q selected
    | true =>
      simp only [d232559, d234094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232560 q = 0) : d234095 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232560, d234095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232560, d234095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232561 q = 0) : d234096 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232561, d234096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232561, d234096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232562 q = 0) : d234097 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232562, d234097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232562, d234097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232566 q = 0) : d234101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232566, d234101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23229 q selected
    | true =>
      simp only [d232566, d234101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232567 q = 0) : d234102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232567, d234102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232567, d234102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232568 q = 0) : d234103 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232568, d234103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232568, d234103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232569 q = 0) : d234104 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232569, d234104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232569, d234104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232570 q = 0) : d234105 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232570, d234105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232570, d234105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232572 q = 0) : d234107 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232572, d234107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232572, d234107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232573 q = 0) : d234108 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232573, d234108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232573, d234108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro23232 (p : Pattern) (selected : d232577 p = 0) : d234112 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232566 q = 0) : d234101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232566, d234101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23229 q selected
    | true =>
      simp only [d232566, d234101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232567 q = 0) : d234102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232567, d234102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232567, d234102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232568 q = 0) : d234103 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232568, d234103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232568, d234103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232569 q = 0) : d234104 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232569, d234104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232569, d234104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232572 q = 0) : d234107 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232572, d234107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232572, d234107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232577 q = 0) : d234112 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232577, d234112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232577, d234112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23233 (p : Pattern) (selected : d232584 p = 0) : d234119 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232574 q = 0) : d234109 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232574, d234109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23230 q selected
    | true =>
      simp only [d232574, d234109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23231 q selected
  have h2 (q : Pattern) (selected : d232575 q = 0) : d234110 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232575, d234110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232575, d234110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232576 q = 0) : d234111 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232576, d234111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232576, d234111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232578 q = 0) : d234113 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232578, d234113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23231 q selected
    | true =>
      simp only [d232578, d234113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23232 q selected
  have h5 (q : Pattern) (selected : d232579 q = 0) : d234114 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232579, d234114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232579, d234114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232580 q = 0) : d234115 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232580, d234115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232580, d234115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232581 q = 0) : d234116 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232581, d234116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232581, d234116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232582 q = 0) : d234117 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232582, d234117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232582, d234117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232583 q = 0) : d234118 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232583, d234118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232583, d234118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232584 q = 0) : d234119 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232584, d234119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232584, d234119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro23234 (p : Pattern) (selected : d232588 p = 0) : d234123 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232578 q = 0) : d234113 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232578, d234113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23231 q selected
    | true =>
      simp only [d232578, d234113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23232 q selected
  have h2 (q : Pattern) (selected : d232579 q = 0) : d234114 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232579, d234114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232579, d234114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232580 q = 0) : d234115 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232580, d234115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232580, d234115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232582 q = 0) : d234117 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232582, d234117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232582, d234117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232587 q = 0) : d234122 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232587, d234122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232587, d234122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232588 q = 0) : d234123 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232588, d234123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232588, d234123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23235 (p : Pattern) (selected : d232594 p = 0) : d234129 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232585 q = 0) : d234120 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232585, d234120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23233 q selected
    | true =>
      simp only [d232585, d234120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232586 q = 0) : d234121 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232586, d234121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232586, d234121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232589 q = 0) : d234124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232589, d234124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23234 q selected
    | true =>
      simp only [d232589, d234124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232590 q = 0) : d234125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232590, d234125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232590, d234125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232591 q = 0) : d234126 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232591, d234126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232591, d234126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232592 q = 0) : d234127 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232592, d234127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232592, d234127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232593 q = 0) : d234128 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232593, d234128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232593, d234128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232594 q = 0) : d234129 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232594, d234129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232594, d234129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro23236 (p : Pattern) (selected : d232598 p = 0) : d234133 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232589 q = 0) : d234124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232589, d234124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23234 q selected
    | true =>
      simp only [d232589, d234124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232590 q = 0) : d234125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232590, d234125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232590, d234125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232595 q = 0) : d234130 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232595, d234130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232595, d234130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232596 q = 0) : d234131 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232596, d234131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232596, d234131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232597 q = 0) : d234132 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232597, d234132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232597, d234132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232598 q = 0) : d234133 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232598, d234133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232598, d234133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23237 (p : Pattern) (selected : d232602 p = 0) : d234193 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1549 q = 0) : d52990 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1549, d52990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro465 q selected
    | true =>
      simp only [d1549, d52990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1550 q = 0) : d52991 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1550, d52991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1550, d52991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232601 q = 0) : d234192 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232601, d234192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232601, d234192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1564 q = 0) : d53005 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro468 q selected
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1565 q = 0) : d53006 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232458 q = 0) : d234099 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d232458, d234099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232458, d234099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232602 q = 0) : d234193 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d232602, d234193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232602, d234193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro23238 (p : Pattern) (selected : d232608 p = 0) : d234199 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232453 q = 0) : d234094 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232453, d234094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23206 q selected
    | true =>
      simp only [d232453, d234094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232454 q = 0) : d234095 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232454, d234095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232454, d234095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232455 q = 0) : d234096 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232455, d234096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232455, d234096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232456 q = 0) : d234097 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232456, d234097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232456, d234097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232460 q = 0) : d234101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232460, d234101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23207 q selected
    | true =>
      simp only [d232460, d234101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232461 q = 0) : d234102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232461, d234102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232461, d234102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232462 q = 0) : d234103 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232462, d234103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232462, d234103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232463 q = 0) : d234104 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232463, d234104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232463, d234104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d232464 q = 0) : d234105 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232464, d234105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232464, d234105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232603 q = 0) : d234194 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232603, d234194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23237 q selected
    | true =>
      simp only [d232603, d234194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d232604 q = 0) : d234195 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232604, d234195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d232604, d234195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d232605 q = 0) : d234196 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232605, d234196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232605, d234196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d232606 q = 0) : d234197 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232606, d234197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232606, d234197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d232607 q = 0) : d234198 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232607, d234198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d232607, d234198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d232608 q = 0) : d234199 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232608, d234199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d232608, d234199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro23239 (p : Pattern) (selected : d232609 p = 0) : d234200 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232603 q = 0) : d234194 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d232603, d234194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23237 q selected
    | true =>
      simp only [d232603, d234194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232604 q = 0) : d234195 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d232604, d234195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d232604, d234195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d232605 q = 0) : d234196 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d232605, d234196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232605, d234196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232606 q = 0) : d234197 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d232606, d234197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232606, d234197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232607 q = 0) : d234198 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d232607, d234198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232607, d234198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232609 q = 0) : d234200 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d232609, d234200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232609, d234200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23240 (p : Pattern) (selected : d232615 p = 0) : d234206 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232468 q = 0) : d234109 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232468, d234109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23208 q selected
    | true =>
      simp only [d232468, d234109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23209 q selected
  have h2 (q : Pattern) (selected : d232469 q = 0) : d234110 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232469, d234110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232469, d234110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232470 q = 0) : d234111 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232470, d234111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232470, d234111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232472 q = 0) : d234113 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232472, d234113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23209 q selected
    | true =>
      simp only [d232472, d234113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23210 q selected
  have h5 (q : Pattern) (selected : d232473 q = 0) : d234114 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232473, d234114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232473, d234114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232474 q = 0) : d234115 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232474, d234115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232474, d234115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232475 q = 0) : d234116 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232475, d234116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232475, d234116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232610 q = 0) : d234201 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232610, d234201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23238 q selected
    | true =>
      simp only [d232610, d234201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23239 q selected
  have h9 (q : Pattern) (selected : d232611 q = 0) : d234202 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d232611, d234202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232611, d234202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d232612 q = 0) : d234203 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d232612, d234203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232612, d234203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d232613 q = 0) : d234204 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d232613, d234204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d232613, d234204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d232614 q = 0) : d234205 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d232614, d234205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232614, d234205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d232615 q = 0) : d234206 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d232615, d234206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d232615, d234206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro23241 (p : Pattern) (selected : d232621 p = 0) : d234212 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232616 q = 0) : d234207 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232616, d234207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23240 q selected
    | true =>
      simp only [d232616, d234207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232617 q = 0) : d234208 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232617, d234208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232617, d234208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232618 q = 0) : d234209 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232618, d234209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232618, d234209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232619 q = 0) : d234210 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232619, d234210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232619, d234210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232620 q = 0) : d234211 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232620, d234211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232620, d234211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232621 q = 0) : d234212 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232621, d234212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232621, d234212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro23242 (p : Pattern) (selected : d232627 p = 0) : d234218 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232516 q = 0) : d234157 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232516, d234157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23219 q selected
    | true =>
      simp only [d232516, d234157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23220 q selected
  have h2 (q : Pattern) (selected : d232517 q = 0) : d234158 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232517, d234158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232517, d234158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232518 q = 0) : d234159 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232518, d234159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232518, d234159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232519 q = 0) : d234160 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232519, d234160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232519, d234160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232526 q = 0) : d234167 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232526, d234167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23221 q selected
    | true =>
      simp only [d232526, d234167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23222 q selected
  have h6 (q : Pattern) (selected : d232527 q = 0) : d234168 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232527, d234168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232527, d234168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232528 q = 0) : d234169 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232528, d234169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232528, d234169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232549 q = 0) : d234190 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232549, d234190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23226 q selected
    | true =>
      simp only [d232549, d234190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23213 q selected
  have h9 (q : Pattern) (selected : d232599 q = 0) : d234134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232599, d234134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23235 q selected
    | true =>
      simp only [d232599, d234134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23236 q selected
  have h10 (q : Pattern) (selected : d232600 q = 0) : d234191 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232600, d234191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d232600, d234191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d232622 q = 0) : d234213 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d232622, d234213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23241 q selected
    | true =>
      simp only [d232622, d234213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d232623 q = 0) : d234214 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d232623, d234214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d232623, d234214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d232624 q = 0) : d234215 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d232624, d234215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d232624, d234215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d232625 q = 0) : d234216 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d232625, d234216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232625, d234216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d232626 q = 0) : d234217 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d232626, d234217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232626, d234217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d232627 q = 0) : d234218 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d232627, d234218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232627, d234218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro23243 (p : Pattern) (selected : d232628 p = 0) : d234219 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232479 q = 0) : d234120 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232479, d234120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23211 q selected
    | true =>
      simp only [d232479, d234120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232480 q = 0) : d234121 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232480, d234121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232480, d234121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232483 q = 0) : d234124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232483, d234124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23212 q selected
    | true =>
      simp only [d232483, d234124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232484 q = 0) : d234125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232484, d234125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232484, d234125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232485 q = 0) : d234126 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232485, d234126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232485, d234126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232486 q = 0) : d234127 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232486, d234127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232486, d234127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232512 q = 0) : d234153 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232512, d234153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232512, d234153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d232628 q = 0) : d234219 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232628, d234219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232628, d234219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23244 (p : Pattern) (selected : d232629 p = 0) : d234220 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232483 q = 0) : d234124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232483, d234124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23212 q selected
    | true =>
      simp only [d232483, d234124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232484 q = 0) : d234125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232484, d234125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232484, d234125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232489 q = 0) : d234130 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232489, d234130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232489, d234130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232490 q = 0) : d234131 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232490, d234131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232490, d234131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232514 q = 0) : d234155 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232514, d234155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232514, d234155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232629 q = 0) : d234220 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232629, d234220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232629, d234220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23245 (p : Pattern) (selected : d232634 p = 0) : d234225 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232479 q = 0) : d234120 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232479, d234120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23211 q selected
    | true =>
      simp only [d232479, d234120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232480 q = 0) : d234121 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232480, d234121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232480, d234121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232483 q = 0) : d234124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232483, d234124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23212 q selected
    | true =>
      simp only [d232483, d234124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232484 q = 0) : d234125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232484, d234125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232484, d234125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232485 q = 0) : d234126 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232485, d234126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232485, d234126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232520 q = 0) : d234161 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232520, d234161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232520, d234161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d232521 q = 0) : d234162 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232521, d234162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232521, d234162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232634 q = 0) : d234225 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232634, d234225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232634, d234225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23246 (p : Pattern) (selected : d232635 p = 0) : d234226 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232483 q = 0) : d234124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232483, d234124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23212 q selected
    | true =>
      simp only [d232483, d234124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232484 q = 0) : d234125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232484, d234125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232484, d234125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232489 q = 0) : d234130 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232489, d234130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232489, d234130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232523 q = 0) : d234164 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232523, d234164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232523, d234164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232524 q = 0) : d234165 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232524, d234165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232524, d234165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232635 q = 0) : d234226 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232635, d234226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232635, d234226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro23247 (p : Pattern) (selected : d232639 p = 0) : d234230 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232543 q = 0) : d234184 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232543, d234184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23225 q selected
    | true =>
      simp only [d232543, d234184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232544 q = 0) : d234185 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232544, d234185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232544, d234185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232479 q = 0) : d234120 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232479, d234120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23211 q selected
    | true =>
      simp only [d232479, d234120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232480 q = 0) : d234121 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232480, d234121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232480, d234121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232545 q = 0) : d234186 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232545, d234186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232545, d234186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232546 q = 0) : d234187 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232546, d234187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232546, d234187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232547 q = 0) : d234188 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232547, d234188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232547, d234188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232639 q = 0) : d234230 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232639, d234230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232639, d234230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23248 (p : Pattern) (selected : d232641 p = 0) : d234142 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232585 q = 0) : d234120 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232585, d234120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23233 q selected
    | true =>
      simp only [d232585, d234120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232586 q = 0) : d234121 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232586, d234121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232586, d234121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232589 q = 0) : d234124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232589, d234124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23234 q selected
    | true =>
      simp only [d232589, d234124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232590 q = 0) : d234125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232590, d234125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232590, d234125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d232591 q = 0) : d234126 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232591, d234126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232591, d234126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d232592 q = 0) : d234127 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232592, d234127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232592, d234127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d232593 q = 0) : d234128 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232593, d234128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d232593, d234128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d232641 q = 0) : d234142 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232641, d234142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d232641, d234142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro23249 (p : Pattern) (selected : d232642 p = 0) : d234143 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d232589 q = 0) : d234124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d232589, d234124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23234 q selected
    | true =>
      simp only [d232589, d234124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d232590 q = 0) : d234125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d232590, d234125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d232590, d234125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d232595 q = 0) : d234130 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d232595, d234130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d232595, d234130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d232596 q = 0) : d234131 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d232596, d234131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d232596, d234131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d232597 q = 0) : d234132 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d232597, d234132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d232597, d234132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d232642 q = 0) : d234143 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d232642, d234143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d232642, d234143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
end NetHack.Soko22Hazard87
