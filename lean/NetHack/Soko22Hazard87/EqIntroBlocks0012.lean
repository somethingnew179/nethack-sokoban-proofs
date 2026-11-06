import NetHack.Soko22Hazard87.EqIntroBlocks0011
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro3000 (p : Pattern) (selected : d70645 p = 0) : d71270 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1908 q = 0) : d53234 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, d53234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro532 q selected
    | true =>
      simp only [d1908, d53234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1909 q = 0) : d53235 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, d53235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1909, d53235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70643 q = 0) : d71268 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70643, d71268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70643, d71268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70644 q = 0) : d71269 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70644, d71269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70644, d71269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70645 q = 0) : d71270 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70645, d71270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70645, d71270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro3001 (p : Pattern) (selected : d70650 p = 0) : d71276 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d70642 q = 0) : d71271 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70642, d71271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2998 q selected
    | true =>
      simp only [d70642, d71271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2999 q selected
  have h2 (q : Pattern) (selected : d70646 q = 0) : d71272 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70646, d71272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3000 q selected
    | true =>
      simp only [d70646, d71272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d70647 q = 0) : d71273 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70647, d71273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70647, d71273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d70648 q = 0) : d71274 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70648, d71274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70648, d71274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d70649 q = 0) : d71275 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70649, d71275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70649, d71275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70650 q = 0) : d71276 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70650, d71276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70650, d71276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3002 (p : Pattern) (selected : d70656 p = 0) : d71282 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d70576 q = 0) : d71209 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70576, d71209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70576, d71209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2984 q selected
  have h2 (q : Pattern) (selected : d70577 q = 0) : d71210 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70577, d71210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70577, d71210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d70584 q = 0) : d71217 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70584, d71217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2984 q selected
    | true =>
      simp only [d70584, d71217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2986 q selected
  have h4 (q : Pattern) (selected : d70585 q = 0) : d71218 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70585, d71218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70585, d71218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70586 q = 0) : d71219 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70586, d71219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70586, d71219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70624 q = 0) : d71253 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70624, d71253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2991 q selected
    | true =>
      simp only [d70624, d71253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2996 q selected
  have h7 (q : Pattern) (selected : d70625 q = 0) : d71254 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70625, d71254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d70625, d71254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d70626 q = 0) : d71255 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70626, d71255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d70626, d71255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d70627 q = 0) : d71256 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70627, d71256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d70627, d71256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d70631 q = 0) : d71260 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70631, d71260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70631, d71260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2997 q selected
  have h11 (q : Pattern) (selected : d70632 q = 0) : d71261 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70632, d71261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d70632, d71261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d70633 q = 0) : d71262 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70633, d71262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d70633, d71262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d70634 q = 0) : d71263 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70634, d71263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d70634, d71263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d70635 q = 0) : d71264 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70635, d71264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d70635, d71264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d70651 q = 0) : d71277 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70651, d71277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70651, d71277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3001 q selected
  have h16 (q : Pattern) (selected : d70652 q = 0) : d71278 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70652, d71278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d70652, d71278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d70653 q = 0) : d71279 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70653, d71279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d70653, d71279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d70654 q = 0) : d71280 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70654, d71280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d70654, d71280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d70655 q = 0) : d71281 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70655, d71281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d70655, d71281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d70656 q = 0) : d71282 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d70656, d71282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d70656, d71282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  exact h20 p selected
theorem eqIntro3003 (p : Pattern) (selected : d70662 p = 0) : d71288 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d70657 q = 0) : d71283 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d70657, d71283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70657, d71283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3002 q selected
  have h2 (q : Pattern) (selected : d70658 q = 0) : d71284 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d70658, d71284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70658, d71284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70659 q = 0) : d71285 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d70659, d71285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70659, d71285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d70660 q = 0) : d71286 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d70660, d71286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70660, d71286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d70661 q = 0) : d71287 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d70661, d71287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70661, d71287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70662 q = 0) : d71288 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d70662, d71288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70662, d71288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3004 (p : Pattern) (selected : d70669 p = 0) : d71295 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2097 q = 0) : d53376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro565 q selected
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2098 q = 0) : d53377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70667 q = 0) : d71293 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70667, d71293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70667, d71293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70668 q = 0) : d71294 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70668, d71294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70668, d71294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70669 q = 0) : d71295 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70669, d71295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70669, d71295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro3005 (p : Pattern) (selected : d70674 p = 0) : d71300 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d70670 q = 0) : d71296 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70670, d71296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70670, d71296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3004 q selected
  have h2 (q : Pattern) (selected : d70671 q = 0) : d71297 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70671, d71297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70671, d71297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d70672 q = 0) : d71298 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70672, d71298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70672, d71298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d70673 q = 0) : d71299 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70673, d71299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70673, d71299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d70674 q = 0) : d71300 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70674, d71300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70674, d71300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro3006 (p : Pattern) (selected : d70677 p = 0) : d71303 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2097 q = 0) : d53376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro565 q selected
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2098 q = 0) : d53377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70667 q = 0) : d71293 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70667, d71293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70667, d71293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70668 q = 0) : d71294 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70668, d71294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70668, d71294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70677 q = 0) : d71303 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70677, d71303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70677, d71303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro3007 (p : Pattern) (selected : d70682 p = 0) : d71308 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d70670 q = 0) : d71296 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70670, d71296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70670, d71296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3004 q selected
  have h2 (q : Pattern) (selected : d70671 q = 0) : d71297 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70671, d71297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70671, d71297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d70672 q = 0) : d71298 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70672, d71298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70672, d71298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d70673 q = 0) : d71299 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70673, d71299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70673, d71299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d70678 q = 0) : d71304 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70678, d71304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70678, d71304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3006 q selected
  have h6 (q : Pattern) (selected : d70679 q = 0) : d71305 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70679, d71305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d70679, d71305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d70680 q = 0) : d71306 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70680, d71306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70680, d71306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d70681 q = 0) : d71307 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70681, d71307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70681, d71307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d70682 q = 0) : d71308 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70682, d71308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70682, d71308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro3008 (p : Pattern) (selected : d70687 p = 0) : d71313 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2097 q = 0) : d53376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro565 q selected
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2098 q = 0) : d53377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70667 q = 0) : d71293 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70667, d71293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70667, d71293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70686 q = 0) : d71312 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70686, d71312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70686, d71312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d70687 q = 0) : d71313 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70687, d71313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70687, d71313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro3009 (p : Pattern) (selected : d70693 p = 0) : d71319 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2097 q = 0) : d53376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro565 q selected
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2098 q = 0) : d53377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70691 q = 0) : d71317 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70691, d71317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70691, d71317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d70692 q = 0) : d71318 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70692, d71318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70692, d71318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70693 q = 0) : d71319 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70693, d71319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70693, d71319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro3010 (p : Pattern) (selected : d70698 p = 0) : d71324 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2093 q = 0) : d53372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro564 q selected
    | true =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2094 q = 0) : d53373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70696 q = 0) : d71322 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70696, d71322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70696, d71322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70697 q = 0) : d71323 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70697, d71323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70697, d71323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70698 q = 0) : d71324 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70698, d71324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70698, d71324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro3011 (p : Pattern) (selected : d70701 p = 0) : d71295 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2263 q = 0) : d53376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2263, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro599 q selected
    | true =>
      simp only [d2263, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2264 q = 0) : d53377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2264, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2264, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70699 q = 0) : d71293 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70699, d71293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70699, d71293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70700 q = 0) : d71294 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70700, d71294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70700, d71294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70701 q = 0) : d71295 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70701, d71295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70701, d71295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro3012 (p : Pattern) (selected : d70707 p = 0) : d71330 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d70688 q = 0) : d71314 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70688, d71314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70688, d71314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3008 q selected
  have h2 (q : Pattern) (selected : d70689 q = 0) : d71315 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70689, d71315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70689, d71315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d70690 q = 0) : d71316 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70690, d71316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70690, d71316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d70694 q = 0) : d71320 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70694, d71320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70694, d71320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3009 q selected
  have h5 (q : Pattern) (selected : d70695 q = 0) : d71321 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70695, d71321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70695, d71321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d70702 q = 0) : d71325 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70702, d71325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3010 q selected
    | true =>
      simp only [d70702, d71325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3011 q selected
  have h7 (q : Pattern) (selected : d70703 q = 0) : d71326 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70703, d71326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3004 q selected
    | true =>
      simp only [d70703, d71326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d70704 q = 0) : d71327 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70704, d71327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d70704, d71327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d70705 q = 0) : d71328 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70705, d71328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d70705, d71328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d70706 q = 0) : d71329 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70706, d71329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70706, d71329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d70707 q = 0) : d71330 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70707, d71330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70707, d71330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro3013 (p : Pattern) (selected : d70708 p = 0) : d71331 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2097 q = 0) : d53376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro565 q selected
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2098 q = 0) : d53377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70667 q = 0) : d71293 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70667, d71293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70667, d71293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70686 q = 0) : d71312 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70686, d71312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70686, d71312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d70708 q = 0) : d71331 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70708, d71331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70708, d71331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro3014 (p : Pattern) (selected : d70712 p = 0) : d71335 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2097 q = 0) : d53376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro565 q selected
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2098 q = 0) : d53377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70691 q = 0) : d71317 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70691, d71317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70691, d71317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d70692 q = 0) : d71318 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70692, d71318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70692, d71318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70712 q = 0) : d71335 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70712, d71335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70712, d71335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro3015 (p : Pattern) (selected : d70715 p = 0) : d71338 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2093 q = 0) : d53372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro564 q selected
    | true =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2094 q = 0) : d53373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70696 q = 0) : d71322 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70696, d71322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70696, d71322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70697 q = 0) : d71323 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70697, d71323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70697, d71323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70715 q = 0) : d71338 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70715, d71338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70715, d71338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro3016 (p : Pattern) (selected : d70716 p = 0) : d71303 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2263 q = 0) : d53376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2263, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro599 q selected
    | true =>
      simp only [d2263, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2264 q = 0) : d53377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2264, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2264, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70699 q = 0) : d71293 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70699, d71293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70699, d71293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70700 q = 0) : d71294 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70700, d71294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70700, d71294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70716 q = 0) : d71303 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70716, d71303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70716, d71303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro3017 (p : Pattern) (selected : d70722 p = 0) : d71344 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d70688 q = 0) : d71314 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70688, d71314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70688, d71314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3008 q selected
  have h2 (q : Pattern) (selected : d70689 q = 0) : d71315 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70689, d71315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70689, d71315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d70690 q = 0) : d71316 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70690, d71316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70690, d71316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d70694 q = 0) : d71320 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70694, d71320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70694, d71320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3009 q selected
  have h5 (q : Pattern) (selected : d70695 q = 0) : d71321 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70695, d71321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70695, d71321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d70702 q = 0) : d71325 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70702, d71325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3010 q selected
    | true =>
      simp only [d70702, d71325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3011 q selected
  have h7 (q : Pattern) (selected : d70703 q = 0) : d71326 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70703, d71326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3004 q selected
    | true =>
      simp only [d70703, d71326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d70704 q = 0) : d71327 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70704, d71327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d70704, d71327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d70705 q = 0) : d71328 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70705, d71328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d70705, d71328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d70706 q = 0) : d71329 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70706, d71329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70706, d71329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d70709 q = 0) : d71332 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70709, d71332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70709, d71332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3013 q selected
  have h12 (q : Pattern) (selected : d70710 q = 0) : d71333 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70710, d71333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d70710, d71333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d70711 q = 0) : d71334 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70711, d71334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70711, d71334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d70713 q = 0) : d71336 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70713, d71336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70713, d71336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3014 q selected
  have h15 (q : Pattern) (selected : d70714 q = 0) : d71337 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70714, d71337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d70714, d71337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d70717 q = 0) : d71339 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70717, d71339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3015 q selected
    | true =>
      simp only [d70717, d71339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3016 q selected
  have h17 (q : Pattern) (selected : d70718 q = 0) : d71340 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70718, d71340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3006 q selected
    | true =>
      simp only [d70718, d71340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d70719 q = 0) : d71341 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70719, d71341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d70719, d71341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d70720 q = 0) : d71342 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70720, d71342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d70720, d71342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d70721 q = 0) : d71343 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70721, d71343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d70721, d71343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d70722 q = 0) : d71344 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70722, d71344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d70722, d71344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro3018 (p : Pattern) (selected : d70729 p = 0) : d71351 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d70717 q = 0) : d71339 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70717, d71339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3015 q selected
    | true =>
      simp only [d70717, d71339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3016 q selected
  have h2 (q : Pattern) (selected : d70718 q = 0) : d71340 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70718, d71340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3006 q selected
    | true =>
      simp only [d70718, d71340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d70719 q = 0) : d71341 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70719, d71341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70719, d71341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d70727 q = 0) : d71349 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70727, d71349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70727, d71349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d70728 q = 0) : d71350 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70728, d71350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70728, d71350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70729 q = 0) : d71351 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70729, d71351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70729, d71351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3019 (p : Pattern) (selected : d70737 p = 0) : d71359 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2378 q = 0) : d53543 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2378, d53543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro620 q selected
    | true =>
      simp only [d2378, d53543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2379 q = 0) : d53544 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2379, d53544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2379, d53544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70735 q = 0) : d71357 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70735, d71357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70735, d71357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70736 q = 0) : d71358 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70736, d71358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70736, d71358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70737 q = 0) : d71359 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70737, d71359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70737, d71359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro3020 (p : Pattern) (selected : d70740 p = 0) : d71362 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2430 q = 0) : d53551 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2430, d53551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro628 q selected
    | true =>
      simp only [d2430, d53551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2431 q = 0) : d53552 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2431, d53552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2431, d53552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70738 q = 0) : d71360 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70738, d71360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70738, d71360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70739 q = 0) : d71361 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70739, d71361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70739, d71361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70740 q = 0) : d71362 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70740, d71362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70740, d71362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro3021 (p : Pattern) (selected : d70744 p = 0) : d71362 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2386 q = 0) : d53551 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2386, d53551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro622 q selected
    | true =>
      simp only [d2386, d53551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2387 q = 0) : d53552 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, d53552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2387, d53552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70742 q = 0) : d71360 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70742, d71360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70742, d71360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70743 q = 0) : d71361 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70743, d71361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70743, d71361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70744 q = 0) : d71362 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70744, d71362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70744, d71362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro3022 (p : Pattern) (selected : d70749 p = 0) : d71368 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d70741 q = 0) : d71363 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70741, d71363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3019 q selected
    | true =>
      simp only [d70741, d71363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3020 q selected
  have h2 (q : Pattern) (selected : d70745 q = 0) : d71364 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70745, d71364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3021 q selected
    | true =>
      simp only [d70745, d71364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d70746 q = 0) : d71365 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70746, d71365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70746, d71365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d70747 q = 0) : d71366 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70747, d71366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70747, d71366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d70748 q = 0) : d71367 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70748, d71367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70748, d71367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70749 q = 0) : d71368 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70749, d71368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70749, d71368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3023 (p : Pattern) (selected : d70755 p = 0) : d71374 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d70675 q = 0) : d71301 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70675, d71301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70675, d71301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3005 q selected
  have h2 (q : Pattern) (selected : d70676 q = 0) : d71302 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70676, d71302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70676, d71302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d70683 q = 0) : d71309 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70683, d71309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3005 q selected
    | true =>
      simp only [d70683, d71309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3007 q selected
  have h4 (q : Pattern) (selected : d70684 q = 0) : d71310 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70684, d71310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70684, d71310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70685 q = 0) : d71311 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70685, d71311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70685, d71311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70723 q = 0) : d71345 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70723, d71345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3012 q selected
    | true =>
      simp only [d70723, d71345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3017 q selected
  have h7 (q : Pattern) (selected : d70724 q = 0) : d71346 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70724, d71346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d70724, d71346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d70725 q = 0) : d71347 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70725, d71347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d70725, d71347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d70726 q = 0) : d71348 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70726, d71348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d70726, d71348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d70730 q = 0) : d71352 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70730, d71352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70730, d71352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3018 q selected
  have h11 (q : Pattern) (selected : d70731 q = 0) : d71353 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70731, d71353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d70731, d71353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d70732 q = 0) : d71354 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70732, d71354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d70732, d71354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d70733 q = 0) : d71355 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70733, d71355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d70733, d71355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d70734 q = 0) : d71356 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70734, d71356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d70734, d71356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d70750 q = 0) : d71369 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70750, d71369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70750, d71369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3022 q selected
  have h16 (q : Pattern) (selected : d70751 q = 0) : d71370 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70751, d71370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d70751, d71370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d70752 q = 0) : d71371 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70752, d71371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d70752, d71371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d70753 q = 0) : d71372 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70753, d71372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d70753, d71372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d70754 q = 0) : d71373 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70754, d71373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d70754, d71373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d70755 q = 0) : d71374 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d70755, d71374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d70755, d71374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  exact h20 p selected
theorem eqIntro3024 (p : Pattern) (selected : d70761 p = 0) : d71380 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d70756 q = 0) : d71375 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d70756, d71375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70756, d71375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3023 q selected
  have h2 (q : Pattern) (selected : d70757 q = 0) : d71376 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d70757, d71376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70757, d71376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70758 q = 0) : d71377 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d70758, d71377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70758, d71377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d70759 q = 0) : d71378 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d70759, d71378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70759, d71378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d70760 q = 0) : d71379 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d70760, d71379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70760, d71379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70761 q = 0) : d71380 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d70761, d71380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70761, d71380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3025 (p : Pattern) (selected : d70767 p = 0) : d71386 p = 1 := by
  have h0 (q : Pattern) (selected : d70372 q = 0) : d71019 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d70372, d71019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2919 q selected
    | true =>
      simp only [d70372, d71019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2940 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d70468 q = 0) : d71108 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d70468, d71108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70468, d71108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2961 q selected
  have h3 (q : Pattern) (selected : d70469 q = 0) : d71109 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d70469, d71109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70469, d71109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d70565 q = 0) : d71198 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d70565, d71198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70565, d71198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2982 q selected
  have h5 (q : Pattern) (selected : d70566 q = 0) : d71199 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d70566, d71199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70566, d71199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70567 q = 0) : d71200 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d70567, d71200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70567, d71200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d70663 q = 0) : d71289 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d70663, d71289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70663, d71289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3003 q selected
  have h8 (q : Pattern) (selected : d70664 q = 0) : d71290 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d70664, d71290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70664, d71290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d70665 q = 0) : d71291 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d70665, d71291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70665, d71291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d70666 q = 0) : d71292 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d70666, d71292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d70666, d71292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d70762 q = 0) : d71381 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d70762, d71381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70762, d71381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3024 q selected
  have h12 (q : Pattern) (selected : d70763 q = 0) : d71382 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d70763, d71382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70763, d71382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d70764 q = 0) : d71383 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d70764, d71383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70764, d71383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d70765 q = 0) : d71384 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d70765, d71384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70765, d71384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d70766 q = 0) : d71385 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d70766, d71385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d70766, d71385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d70767 q = 0) : d71386 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d70767, d71386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d70767, d71386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro3026 (p : Pattern) (selected : d70773 p = 0) : d71392 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d70768 q = 0) : d71387 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d70768, d71387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3025 q selected
    | true =>
      simp only [d70768, d71387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d70769 q = 0) : d71388 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d70769, d71388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70769, d71388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d70770 q = 0) : d71389 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d70770, d71389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70770, d71389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70771 q = 0) : d71390 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d70771, d71390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70771, d71390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70772 q = 0) : d71391 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d70772, d71391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70772, d71391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d70773 q = 0) : d71392 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d70773, d71392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d70773, d71392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3027 (p : Pattern) (selected : d70779 p = 0) : d71398 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d70774 q = 0) : d71393 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d70774, d71393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3026 q selected
    | true =>
      simp only [d70774, d71393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d70775 q = 0) : d71394 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d70775, d71394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70775, d71394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d70776 q = 0) : d71395 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d70776, d71395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70776, d71395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70777 q = 0) : d71396 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d70777, d71396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70777, d71396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70778 q = 0) : d71397 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d70778, d71397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70778, d71397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d70779 q = 0) : d71398 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d70779, d71398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d70779, d71398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3028 (p : Pattern) (selected : d70785 p = 0) : d71404 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d70780 q = 0) : d71399 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d70780, d71399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3027 q selected
    | true =>
      simp only [d70780, d71399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d70781 q = 0) : d71400 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d70781, d71400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70781, d71400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d70782 q = 0) : d71401 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d70782, d71401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70782, d71401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70783 q = 0) : d71402 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d70783, d71402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70783, d71402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70784 q = 0) : d71403 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d70784, d71403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70784, d71403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d70785 q = 0) : d71404 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d70785, d71404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d70785, d71404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3029 (p : Pattern) (selected : d70791 p = 0) : d71410 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d70786 q = 0) : d71405 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d70786, d71405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3028 q selected
    | true =>
      simp only [d70786, d71405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d70787 q = 0) : d71406 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d70787, d71406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70787, d71406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d70788 q = 0) : d71407 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d70788, d71407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70788, d71407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70789 q = 0) : d71408 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d70789, d71408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70789, d71408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70790 q = 0) : d71409 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d70790, d71409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70790, d71409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d70791 q = 0) : d71410 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d70791, d71410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d70791, d71410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3030 (p : Pattern) (selected : d70797 p = 0) : d71416 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d70792 q = 0) : d71411 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d70792, d71411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3029 q selected
    | true =>
      simp only [d70792, d71411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d70793 q = 0) : d71412 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d70793, d71412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70793, d71412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d70794 q = 0) : d71413 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d70794, d71413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70794, d71413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70795 q = 0) : d71414 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d70795, d71414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70795, d71414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70796 q = 0) : d71415 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d70796, d71415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70796, d71415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d70797 q = 0) : d71416 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d70797, d71416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d70797, d71416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3031 (p : Pattern) (selected : d70803 p = 0) : d71422 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d70798 q = 0) : d71417 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d70798, d71417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3030 q selected
    | true =>
      simp only [d70798, d71417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d70799 q = 0) : d71418 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d70799, d71418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70799, d71418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d70800 q = 0) : d71419 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d70800, d71419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70800, d71419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70801 q = 0) : d71420 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d70801, d71420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70801, d71420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70802 q = 0) : d71421 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d70802, d71421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70802, d71421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d70803 q = 0) : d71422 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d70803, d71422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d70803, d71422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3032 (p : Pattern) (selected : d70809 p = 0) : d71428 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d70804 q = 0) : d71423 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d70804, d71423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3031 q selected
    | true =>
      simp only [d70804, d71423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d70805 q = 0) : d71424 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d70805, d71424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70805, d71424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d70806 q = 0) : d71425 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d70806, d71425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70806, d71425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70807 q = 0) : d71426 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d70807, d71426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70807, d71426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70808 q = 0) : d71427 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d70808, d71427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70808, d71427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d70809 q = 0) : d71428 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d70809, d71428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d70809, d71428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3033 (p : Pattern) (selected : d70222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3 q selected
    | true =>
      simp only [d182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d183 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70220 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70221 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70222 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro3034 (p : Pattern) (selected : d70227 p = 1) : d72179 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70211 q = 1) : d70211 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d70216 q = 1) : d70216 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d70219 q = 1) : d70219 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d70223 q = 1) : d72175 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70223, d72175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70223, d72175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3033 q selected
  have h5 (q : Pattern) (selected : d70152 q = 1) : d70152 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d70224 q = 1) : d72176 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70224, d72176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70224, d72176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d70225 q = 1) : d72177 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70225, d72177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70225, d72177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d70226 q = 1) : d72178 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70226, d72178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70226, d72178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d70227 q = 1) : d72179 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70227, d72179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70227, d72179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro3035 (p : Pattern) (selected : d70236 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3 q selected
    | true =>
      simp only [d182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d183 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70220 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70221 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70236 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro3036 (p : Pattern) (selected : d70241 p = 1) : d72184 p = 1 := by
  have h0 (q : Pattern) (selected : d70211 q = 1) : d70211 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70216 q = 1) : d70216 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d70219 q = 1) : d70219 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d70223 q = 1) : d72175 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70223, d72175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70223, d72175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3033 q selected
  have h4 (q : Pattern) (selected : d70152 q = 1) : d70152 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d70224 q = 1) : d72176 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70224, d72176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70224, d72176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70225 q = 1) : d72177 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70225, d72177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70225, d72177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d70226 q = 1) : d72178 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70226, d72178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70226, d72178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d70231 q = 1) : d70231 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d70234 q = 1) : d70234 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d70235 q = 1) : d70235 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d70237 q = 1) : d72180 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70237, d72180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d70237, d72180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3035 q selected
  have h12 (q : Pattern) (selected : d70158 q = 1) : d70158 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d70238 q = 1) : d72181 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70238, d72181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d70238, d72181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d70239 q = 1) : d72182 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70239, d72182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d70239, d72182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d70240 q = 1) : d72183 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70240, d72183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d70240, d72183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d70241 q = 1) : d72184 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70241, d72184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d70241, d72184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro3037 (p : Pattern) (selected : d70248 p = 1) : d72191 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70235 q = 1) : d70235 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d70237 q = 1) : d72180 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70237, d72180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70237, d72180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3035 q selected
  have h3 (q : Pattern) (selected : d70158 q = 1) : d70158 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d70238 q = 1) : d72181 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70238, d72181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70238, d72181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d70246 q = 1) : d72189 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70246, d72189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70246, d72189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70247 q = 1) : d72190 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70247, d72190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70247, d72190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d70248 q = 1) : d72191 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70248, d72191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70248, d72191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro3038 (p : Pattern) (selected : d70259 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10 q selected
    | true =>
      simp only [d257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70257 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70258 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70259 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro3039 (p : Pattern) (selected : d70264 p = 1) : d72201 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70256 q = 1) : d70256 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d70260 q = 1) : d72197 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70260, d72197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70260, d72197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3038 q selected
  have h3 (q : Pattern) (selected : d70176 q = 1) : d70176 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d70261 q = 1) : d72198 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70261, d72198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70261, d72198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d70262 q = 1) : d72199 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70262, d72199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70262, d72199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70263 q = 1) : d72200 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70263, d72200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70263, d72200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d70264 q = 1) : d72201 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70264, d72201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70264, d72201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro3040 (p : Pattern) (selected : d70270 p = 1) : d72207 p = 1 := by
  have h0 (q : Pattern) (selected : d70206 q = 1) : d70206 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70242 q = 1) : d72185 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70242, d72185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3034 q selected
    | true =>
      simp only [d70242, d72185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3036 q selected
  have h2 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d70243 q = 1) : d72186 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70243, d72186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70243, d72186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d70244 q = 1) : d72187 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70244, d72187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70244, d72187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h5 (q : Pattern) (selected : d70245 q = 1) : d72188 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70245, d72188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70245, d72188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70249 q = 1) : d72192 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70249, d72192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70249, d72192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3037 q selected
  have h7 (q : Pattern) (selected : d70250 q = 1) : d72193 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70250, d72193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d70250, d72193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h8 (q : Pattern) (selected : d70251 q = 1) : d72194 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70251, d72194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d70251, d72194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h9 (q : Pattern) (selected : d70252 q = 1) : d72195 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70252, d72195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d70252, d72195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h10 (q : Pattern) (selected : d70253 q = 1) : d72196 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70253, d72196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d70253, d72196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d70265 q = 1) : d72202 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70265, d72202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70265, d72202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3039 q selected
  have h12 (q : Pattern) (selected : d70266 q = 1) : d72203 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70266, d72203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d70266, d72203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h13 (q : Pattern) (selected : d70267 q = 1) : d72204 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70267, d72204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d70267, d72204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h14 (q : Pattern) (selected : d70268 q = 1) : d72205 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70268, d72205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d70268, d72205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h15 (q : Pattern) (selected : d70269 q = 1) : d72206 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70269, d72206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d70269, d72206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h16 (q : Pattern) (selected : d70270 q = 1) : d72207 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d70270, d72207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d70270, d72207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro3041 (p : Pattern) (selected : d70276 p = 1) : d72213 p = 1 := by
  have h0 (q : Pattern) (selected : d70191 q = 1) : d70191 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d70271 q = 1) : d72208 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d70271, d72208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70271, d72208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3040 q selected
  have h3 (q : Pattern) (selected : d70272 q = 1) : d72209 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d70272, d72209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70272, d72209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d70273 q = 1) : d72210 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d70273, d72210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70273, d72210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d70274 q = 1) : d72211 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d70274, d72211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70274, d72211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70275 q = 1) : d72212 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d70275, d72212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70275, d72212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d70276 q = 1) : d72213 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d70276, d72213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70276, d72213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro3042 (p : Pattern) (selected : d70311 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d591 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33 q selected
    | true =>
      simp only [d591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d592 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70309 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70310 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70311 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro3043 (p : Pattern) (selected : d70317 p = 1) : d72218 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70300 q = 1) : d70300 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d70305 q = 1) : d70305 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d70308 q = 1) : d70308 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d70312 q = 1) : d72214 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70312, d72214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70312, d72214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3042 q selected
  have h5 (q : Pattern) (selected : d70313 q = 1) : d70313 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d70314 q = 1) : d72215 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70314, d72215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70314, d72215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d70315 q = 1) : d72216 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70315, d72216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70315, d72216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d70316 q = 1) : d72217 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70316, d72217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70316, d72217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d70317 q = 1) : d72218 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70317, d72218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70317, d72218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro3044 (p : Pattern) (selected : d70326 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d591 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33 q selected
    | true =>
      simp only [d591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d592 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70309 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70310 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70326 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro3045 (p : Pattern) (selected : d70332 p = 1) : d72223 p = 1 := by
  have h0 (q : Pattern) (selected : d70300 q = 1) : d70300 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70305 q = 1) : d70305 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d70308 q = 1) : d70308 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d70312 q = 1) : d72214 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70312, d72214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70312, d72214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3042 q selected
  have h4 (q : Pattern) (selected : d70313 q = 1) : d70313 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d70314 q = 1) : d72215 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70314, d72215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70314, d72215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70315 q = 1) : d72216 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70315, d72216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70315, d72216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d70316 q = 1) : d72217 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70316, d72217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70316, d72217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d70321 q = 1) : d70321 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d70324 q = 1) : d70324 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d70325 q = 1) : d70325 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d70327 q = 1) : d72219 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70327, d72219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d70327, d72219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3044 q selected
  have h12 (q : Pattern) (selected : d70328 q = 1) : d70328 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d70329 q = 1) : d72220 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70329, d72220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d70329, d72220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d70330 q = 1) : d72221 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70330, d72221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d70330, d72221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d70331 q = 1) : d72222 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70331, d72222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d70331, d72222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d70332 q = 1) : d72223 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70332, d72223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d70332, d72223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro3046 (p : Pattern) (selected : d70339 p = 1) : d72230 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70325 q = 1) : d70325 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d70327 q = 1) : d72219 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70327, d72219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70327, d72219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3044 q selected
  have h3 (q : Pattern) (selected : d70328 q = 1) : d70328 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d70329 q = 1) : d72220 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70329, d72220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70329, d72220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d70337 q = 1) : d72228 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70337, d72228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70337, d72228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70338 q = 1) : d72229 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70338, d72229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70338, d72229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d70339 q = 1) : d72230 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70339, d72230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70339, d72230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro3047 (p : Pattern) (selected : d70350 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d708 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro43 q selected
    | true =>
      simp only [d708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d709 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70348 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70349 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70350 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro3048 (p : Pattern) (selected : d70359 p = 1) : d72240 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70347 q = 1) : d70347 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d70351 q = 1) : d72236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70351, d72236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70351, d72236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3047 q selected
  have h3 (q : Pattern) (selected : d70355 q = 1) : d70355 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d70356 q = 1) : d72237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70356, d72237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70356, d72237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d70357 q = 1) : d72238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70357, d72238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70357, d72238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70358 q = 1) : d72239 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70358, d72239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70358, d72239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d70359 q = 1) : d72240 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70359, d72240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70359, d72240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro3049 (p : Pattern) (selected : d70365 p = 1) : d72246 p = 1 := by
  have h0 (q : Pattern) (selected : d70295 q = 1) : d70295 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70333 q = 1) : d72224 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70333, d72224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3043 q selected
    | true =>
      simp only [d70333, d72224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3045 q selected
  have h2 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d70334 q = 1) : d72225 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70334, d72225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70334, d72225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d70335 q = 1) : d72226 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70335, d72226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70335, d72226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h5 (q : Pattern) (selected : d70336 q = 1) : d72227 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70336, d72227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70336, d72227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70340 q = 1) : d72231 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70340, d72231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70340, d72231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3046 q selected
  have h7 (q : Pattern) (selected : d70341 q = 1) : d72232 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70341, d72232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d70341, d72232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h8 (q : Pattern) (selected : d70342 q = 1) : d72233 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70342, d72233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d70342, d72233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h9 (q : Pattern) (selected : d70343 q = 1) : d72234 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70343, d72234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d70343, d72234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h10 (q : Pattern) (selected : d70344 q = 1) : d72235 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70344, d72235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d70344, d72235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d70360 q = 1) : d72241 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70360, d72241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70360, d72241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3048 q selected
  have h12 (q : Pattern) (selected : d70361 q = 1) : d72242 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70361, d72242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d70361, d72242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h13 (q : Pattern) (selected : d70362 q = 1) : d72243 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70362, d72243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d70362, d72243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h14 (q : Pattern) (selected : d70363 q = 1) : d72244 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70363, d72244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d70363, d72244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h15 (q : Pattern) (selected : d70364 q = 1) : d72245 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70364, d72245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d70364, d72245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h16 (q : Pattern) (selected : d70365 q = 1) : d72246 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d70365, d72246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d70365, d72246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro3050 (p : Pattern) (selected : d70371 p = 1) : d72252 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70366 q = 1) : d72247 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d70366, d72247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70366, d72247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3049 q selected
  have h2 (q : Pattern) (selected : d70367 q = 1) : d72248 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d70367, d72248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70367, d72248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70368 q = 1) : d72249 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d70368, d72249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70368, d72249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d70369 q = 1) : d72250 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d70369, d72250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70369, d72250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d70370 q = 1) : d72251 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d70370, d72251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70370, d72251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70371 q = 1) : d72252 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d70371, d72252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70371, d72252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3051 (p : Pattern) (selected : d70407 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d897 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro57 q selected
    | true =>
      simp only [d897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d898 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70405 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70406 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70407 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro3052 (p : Pattern) (selected : d70413 p = 1) : d72258 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70396 q = 1) : d70396 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d70401 q = 1) : d70401 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d70404 q = 1) : d70404 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d70408 q = 1) : d72254 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70408, d72254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70408, d72254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3051 q selected
  have h5 (q : Pattern) (selected : d70409 q = 1) : d70409 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d70410 q = 1) : d72255 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70410, d72255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70410, d72255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d70411 q = 1) : d72256 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70411, d72256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70411, d72256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d70412 q = 1) : d72257 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70412, d72257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70412, d72257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d70413 q = 1) : d72258 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70413, d72258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70413, d72258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro3053 (p : Pattern) (selected : d70422 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d897 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro57 q selected
    | true =>
      simp only [d897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d898 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70405 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70406 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70422 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro3054 (p : Pattern) (selected : d70428 p = 1) : d72263 p = 1 := by
  have h0 (q : Pattern) (selected : d70396 q = 1) : d70396 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70401 q = 1) : d70401 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d70404 q = 1) : d70404 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d70408 q = 1) : d72254 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70408, d72254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70408, d72254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3051 q selected
  have h4 (q : Pattern) (selected : d70409 q = 1) : d70409 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d70410 q = 1) : d72255 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70410, d72255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70410, d72255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70411 q = 1) : d72256 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70411, d72256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70411, d72256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d70412 q = 1) : d72257 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70412, d72257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70412, d72257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d70417 q = 1) : d70417 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d70420 q = 1) : d70420 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d70421 q = 1) : d70421 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d70423 q = 1) : d72259 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70423, d72259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d70423, d72259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3053 q selected
  have h12 (q : Pattern) (selected : d70424 q = 1) : d70424 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d70425 q = 1) : d72260 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70425, d72260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d70425, d72260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d70426 q = 1) : d72261 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70426, d72261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d70426, d72261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d70427 q = 1) : d72262 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70427, d72262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d70427, d72262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d70428 q = 1) : d72263 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70428, d72263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d70428, d72263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro3055 (p : Pattern) (selected : d70435 p = 1) : d72270 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70421 q = 1) : d70421 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d70423 q = 1) : d72259 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70423, d72259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70423, d72259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3053 q selected
  have h3 (q : Pattern) (selected : d70424 q = 1) : d70424 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d70425 q = 1) : d72260 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70425, d72260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70425, d72260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d70433 q = 1) : d72268 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70433, d72268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70433, d72268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70434 q = 1) : d72269 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70434, d72269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70434, d72269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d70435 q = 1) : d72270 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70435, d72270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70435, d72270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro3056 (p : Pattern) (selected : d70446 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1041 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro69 q selected
    | true =>
      simp only [d1041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1042 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70444 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70445 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70446 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro3057 (p : Pattern) (selected : d70455 p = 1) : d72280 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70443 q = 1) : d70443 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d70447 q = 1) : d72276 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70447, d72276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70447, d72276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3056 q selected
  have h3 (q : Pattern) (selected : d70451 q = 1) : d70451 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d70452 q = 1) : d72277 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70452, d72277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70452, d72277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d70453 q = 1) : d72278 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70453, d72278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70453, d72278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70454 q = 1) : d72279 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70454, d72279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70454, d72279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d70455 q = 1) : d72280 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70455, d72280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70455, d72280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro3058 (p : Pattern) (selected : d70461 p = 1) : d72286 p = 1 := by
  have h0 (q : Pattern) (selected : d70391 q = 1) : d70391 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70429 q = 1) : d72264 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70429, d72264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3052 q selected
    | true =>
      simp only [d70429, d72264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3054 q selected
  have h2 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d70430 q = 1) : d72265 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70430, d72265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70430, d72265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d70431 q = 1) : d72266 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70431, d72266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70431, d72266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h5 (q : Pattern) (selected : d70432 q = 1) : d72267 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70432, d72267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70432, d72267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70436 q = 1) : d72271 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70436, d72271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70436, d72271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3055 q selected
  have h7 (q : Pattern) (selected : d70437 q = 1) : d72272 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70437, d72272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d70437, d72272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h8 (q : Pattern) (selected : d70438 q = 1) : d72273 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70438, d72273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d70438, d72273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h9 (q : Pattern) (selected : d70439 q = 1) : d72274 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70439, d72274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d70439, d72274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h10 (q : Pattern) (selected : d70440 q = 1) : d72275 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70440, d72275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d70440, d72275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d70456 q = 1) : d72281 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70456, d72281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70456, d72281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3057 q selected
  have h12 (q : Pattern) (selected : d70457 q = 1) : d72282 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70457, d72282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d70457, d72282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h13 (q : Pattern) (selected : d70458 q = 1) : d72283 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70458, d72283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d70458, d72283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h14 (q : Pattern) (selected : d70459 q = 1) : d72284 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70459, d72284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d70459, d72284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h15 (q : Pattern) (selected : d70460 q = 1) : d72285 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70460, d72285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d70460, d72285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h16 (q : Pattern) (selected : d70461 q = 1) : d72286 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d70461, d72286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d70461, d72286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro3059 (p : Pattern) (selected : d70467 p = 1) : d72292 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70462 q = 1) : d72287 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d70462, d72287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70462, d72287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3058 q selected
  have h2 (q : Pattern) (selected : d70463 q = 1) : d72288 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d70463, d72288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70463, d72288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70464 q = 1) : d72289 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d70464, d72289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70464, d72289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d70465 q = 1) : d72290 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d70465, d72290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70465, d72290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d70466 q = 1) : d72291 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d70466, d72291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70466, d72291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70467 q = 1) : d72292 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d70467, d72292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70467, d72292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3060 (p : Pattern) (selected : d70504 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1308 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro87 q selected
    | true =>
      simp only [d1308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1309 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70502 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70503 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70504 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro3061 (p : Pattern) (selected : d70510 p = 1) : d72299 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70493 q = 1) : d70493 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d70498 q = 1) : d70498 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d70501 q = 1) : d70501 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d70505 q = 1) : d72295 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70505, d72295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70505, d72295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3060 q selected
  have h5 (q : Pattern) (selected : d70506 q = 1) : d70506 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d70507 q = 1) : d72296 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70507, d72296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70507, d72296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d70508 q = 1) : d72297 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70508, d72297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70508, d72297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d70509 q = 1) : d72298 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70509, d72298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70509, d72298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d70510 q = 1) : d72299 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70510, d72299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70510, d72299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro3062 (p : Pattern) (selected : d70519 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1308 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro87 q selected
    | true =>
      simp only [d1308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1309 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70502 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70503 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70519 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro3063 (p : Pattern) (selected : d70525 p = 1) : d72304 p = 1 := by
  have h0 (q : Pattern) (selected : d70493 q = 1) : d70493 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70498 q = 1) : d70498 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d70501 q = 1) : d70501 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d70505 q = 1) : d72295 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70505, d72295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70505, d72295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3060 q selected
  have h4 (q : Pattern) (selected : d70506 q = 1) : d70506 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d70507 q = 1) : d72296 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70507, d72296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70507, d72296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70508 q = 1) : d72297 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70508, d72297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70508, d72297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d70509 q = 1) : d72298 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70509, d72298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70509, d72298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d70514 q = 1) : d70514 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d70517 q = 1) : d70517 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d70518 q = 1) : d70518 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d70520 q = 1) : d72300 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70520, d72300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d70520, d72300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3062 q selected
  have h12 (q : Pattern) (selected : d70521 q = 1) : d70521 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d70522 q = 1) : d72301 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70522, d72301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d70522, d72301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d70523 q = 1) : d72302 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70523, d72302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d70523, d72302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d70524 q = 1) : d72303 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70524, d72303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d70524, d72303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d70525 q = 1) : d72304 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70525, d72304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d70525, d72304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro3064 (p : Pattern) (selected : d70532 p = 1) : d72311 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70518 q = 1) : d70518 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d70520 q = 1) : d72300 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70520, d72300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70520, d72300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3062 q selected
  have h3 (q : Pattern) (selected : d70521 q = 1) : d70521 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d70522 q = 1) : d72301 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70522, d72301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70522, d72301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d70530 q = 1) : d72309 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70530, d72309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70530, d72309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70531 q = 1) : d72310 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70531, d72310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70531, d72310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d70532 q = 1) : d72311 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70532, d72311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70532, d72311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro3065 (p : Pattern) (selected : d70543 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1475 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro99 q selected
    | true =>
      simp only [d1475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1476 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70541 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70542 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70543 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro3066 (p : Pattern) (selected : d70552 p = 1) : d72321 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70540 q = 1) : d70540 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d70544 q = 1) : d72317 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70544, d72317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70544, d72317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3065 q selected
  have h3 (q : Pattern) (selected : d70548 q = 1) : d70548 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d70549 q = 1) : d72318 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70549, d72318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70549, d72318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d70550 q = 1) : d72319 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70550, d72319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70550, d72319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70551 q = 1) : d72320 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70551, d72320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70551, d72320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d70552 q = 1) : d72321 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70552, d72321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70552, d72321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro3067 (p : Pattern) (selected : d70558 p = 1) : d72327 p = 1 := by
  have h0 (q : Pattern) (selected : d70488 q = 1) : d70488 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70526 q = 1) : d72305 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70526, d72305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3061 q selected
    | true =>
      simp only [d70526, d72305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3063 q selected
  have h2 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d70527 q = 1) : d72306 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70527, d72306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70527, d72306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d70528 q = 1) : d72307 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70528, d72307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70528, d72307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h5 (q : Pattern) (selected : d70529 q = 1) : d72308 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70529, d72308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70529, d72308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70533 q = 1) : d72312 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70533, d72312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70533, d72312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3064 q selected
  have h7 (q : Pattern) (selected : d70534 q = 1) : d72313 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70534, d72313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d70534, d72313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h8 (q : Pattern) (selected : d70535 q = 1) : d72314 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70535, d72314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d70535, d72314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h9 (q : Pattern) (selected : d70536 q = 1) : d72315 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70536, d72315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d70536, d72315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h10 (q : Pattern) (selected : d70537 q = 1) : d72316 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70537, d72316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d70537, d72316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d70553 q = 1) : d72322 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70553, d72322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70553, d72322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3066 q selected
  have h12 (q : Pattern) (selected : d70554 q = 1) : d72323 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70554, d72323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d70554, d72323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h13 (q : Pattern) (selected : d70555 q = 1) : d72324 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70555, d72324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d70555, d72324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h14 (q : Pattern) (selected : d70556 q = 1) : d72325 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70556, d72325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d70556, d72325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h15 (q : Pattern) (selected : d70557 q = 1) : d72326 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70557, d72326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d70557, d72326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h16 (q : Pattern) (selected : d70558 q = 1) : d72327 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d70558, d72327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d70558, d72327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro3068 (p : Pattern) (selected : d70564 p = 1) : d72333 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70559 q = 1) : d72328 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d70559, d72328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70559, d72328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3067 q selected
  have h2 (q : Pattern) (selected : d70560 q = 1) : d72329 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d70560, d72329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70560, d72329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70561 q = 1) : d72330 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d70561, d72330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70561, d72330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d70562 q = 1) : d72331 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d70562, d72331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70562, d72331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d70563 q = 1) : d72332 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d70563, d72332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70563, d72332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70564 q = 1) : d72333 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d70564, d72333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70564, d72333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3069 (p : Pattern) (selected : d70602 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1785 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro123 q selected
    | true =>
      simp only [d1785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1786 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70600 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70601 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70602 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro3070 (p : Pattern) (selected : d70608 p = 1) : d72341 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70591 q = 1) : d70591 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d70596 q = 1) : d70596 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d70599 q = 1) : d70599 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d70603 q = 1) : d72337 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70603, d72337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70603, d72337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3069 q selected
  have h5 (q : Pattern) (selected : d70604 q = 1) : d70604 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d70605 q = 1) : d72338 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70605, d72338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70605, d72338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d70606 q = 1) : d72339 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70606, d72339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70606, d72339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d70607 q = 1) : d72340 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70607, d72340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70607, d72340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d70608 q = 1) : d72341 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70608, d72341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70608, d72341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro3071 (p : Pattern) (selected : d70617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1785 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro123 q selected
    | true =>
      simp only [d1785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1786 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70600 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70601 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70617 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro3072 (p : Pattern) (selected : d70623 p = 1) : d72346 p = 1 := by
  have h0 (q : Pattern) (selected : d70591 q = 1) : d70591 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70596 q = 1) : d70596 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d70599 q = 1) : d70599 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d70603 q = 1) : d72337 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70603, d72337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70603, d72337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3069 q selected
  have h4 (q : Pattern) (selected : d70604 q = 1) : d70604 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d70605 q = 1) : d72338 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70605, d72338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70605, d72338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70606 q = 1) : d72339 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70606, d72339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70606, d72339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d70607 q = 1) : d72340 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70607, d72340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70607, d72340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d70612 q = 1) : d70612 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d70615 q = 1) : d70615 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d70616 q = 1) : d70616 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d70618 q = 1) : d72342 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70618, d72342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d70618, d72342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3071 q selected
  have h12 (q : Pattern) (selected : d70619 q = 1) : d70619 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d70620 q = 1) : d72343 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70620, d72343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d70620, d72343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d70621 q = 1) : d72344 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70621, d72344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d70621, d72344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d70622 q = 1) : d72345 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70622, d72345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d70622, d72345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d70623 q = 1) : d72346 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70623, d72346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d70623, d72346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro3073 (p : Pattern) (selected : d70630 p = 1) : d72353 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70616 q = 1) : d70616 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d70618 q = 1) : d72342 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70618, d72342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70618, d72342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3071 q selected
  have h3 (q : Pattern) (selected : d70619 q = 1) : d70619 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d70620 q = 1) : d72343 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70620, d72343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70620, d72343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d70628 q = 1) : d72351 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70628, d72351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70628, d72351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70629 q = 1) : d72352 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70629, d72352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70629, d72352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d70630 q = 1) : d72353 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70630, d72353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70630, d72353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro3074 (p : Pattern) (selected : d70641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1952 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro135 q selected
    | true =>
      simp only [d1952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1953 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70639 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70640 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70641 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro3075 (p : Pattern) (selected : d70650 p = 1) : d72363 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70638 q = 1) : d70638 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d70642 q = 1) : d72359 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70642, d72359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70642, d72359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3074 q selected
  have h3 (q : Pattern) (selected : d70646 q = 1) : d70646 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d70647 q = 1) : d72360 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70647, d72360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70647, d72360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d70648 q = 1) : d72361 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70648, d72361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70648, d72361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70649 q = 1) : d72362 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70649, d72362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70649, d72362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d70650 q = 1) : d72363 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70650, d72363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70650, d72363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro3076 (p : Pattern) (selected : d70656 p = 1) : d72369 p = 1 := by
  have h0 (q : Pattern) (selected : d70586 q = 1) : d70586 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70624 q = 1) : d72347 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70624, d72347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3070 q selected
    | true =>
      simp only [d70624, d72347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3072 q selected
  have h2 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d70625 q = 1) : d72348 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70625, d72348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70625, d72348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d70626 q = 1) : d72349 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70626, d72349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70626, d72349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h5 (q : Pattern) (selected : d70627 q = 1) : d72350 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70627, d72350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70627, d72350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70631 q = 1) : d72354 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70631, d72354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70631, d72354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3073 q selected
  have h7 (q : Pattern) (selected : d70632 q = 1) : d72355 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70632, d72355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d70632, d72355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h8 (q : Pattern) (selected : d70633 q = 1) : d72356 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70633, d72356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d70633, d72356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h9 (q : Pattern) (selected : d70634 q = 1) : d72357 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70634, d72357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d70634, d72357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h10 (q : Pattern) (selected : d70635 q = 1) : d72358 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70635, d72358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d70635, d72358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d70651 q = 1) : d72364 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70651, d72364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70651, d72364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3075 q selected
  have h12 (q : Pattern) (selected : d70652 q = 1) : d72365 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70652, d72365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d70652, d72365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h13 (q : Pattern) (selected : d70653 q = 1) : d72366 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70653, d72366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d70653, d72366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h14 (q : Pattern) (selected : d70654 q = 1) : d72367 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70654, d72367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d70654, d72367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h15 (q : Pattern) (selected : d70655 q = 1) : d72368 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70655, d72368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d70655, d72368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h16 (q : Pattern) (selected : d70656 q = 1) : d72369 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d70656, d72369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d70656, d72369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro3077 (p : Pattern) (selected : d70662 p = 1) : d72375 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70657 q = 1) : d72370 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d70657, d72370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70657, d72370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3076 q selected
  have h2 (q : Pattern) (selected : d70658 q = 1) : d72371 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d70658, d72371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70658, d72371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70659 q = 1) : d72372 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d70659, d72372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70659, d72372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d70660 q = 1) : d72373 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d70660, d72373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70660, d72373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d70661 q = 1) : d72374 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d70661, d72374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70661, d72374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70662 q = 1) : d72375 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d70662, d72375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70662, d72375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3078 (p : Pattern) (selected : d70701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2263 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro160 q selected
    | true =>
      simp only [d2263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2264 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70699 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70700 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70701 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro3079 (p : Pattern) (selected : d70707 p = 1) : d72384 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70690 q = 1) : d70690 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d70695 q = 1) : d70695 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d70698 q = 1) : d70698 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d70702 q = 1) : d72380 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70702, d72380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70702, d72380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3078 q selected
  have h5 (q : Pattern) (selected : d70703 q = 1) : d70703 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d70704 q = 1) : d72381 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70704, d72381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70704, d72381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d70705 q = 1) : d72382 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70705, d72382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70705, d72382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d70706 q = 1) : d72383 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70706, d72383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70706, d72383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d70707 q = 1) : d72384 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70707, d72384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70707, d72384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro3080 (p : Pattern) (selected : d70716 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2263 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro160 q selected
    | true =>
      simp only [d2263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2264 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70699 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70700 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70716 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro3081 (p : Pattern) (selected : d70722 p = 1) : d72389 p = 1 := by
  have h0 (q : Pattern) (selected : d70690 q = 1) : d70690 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70695 q = 1) : d70695 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d70698 q = 1) : d70698 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d70702 q = 1) : d72380 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70702, d72380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70702, d72380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3078 q selected
  have h4 (q : Pattern) (selected : d70703 q = 1) : d70703 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d70704 q = 1) : d72381 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70704, d72381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70704, d72381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70705 q = 1) : d72382 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70705, d72382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70705, d72382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d70706 q = 1) : d72383 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70706, d72383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70706, d72383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d70711 q = 1) : d70711 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d70714 q = 1) : d70714 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d70715 q = 1) : d70715 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d70717 q = 1) : d72385 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70717, d72385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d70717, d72385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3080 q selected
  have h12 (q : Pattern) (selected : d70718 q = 1) : d70718 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d70719 q = 1) : d72386 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70719, d72386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d70719, d72386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d70720 q = 1) : d72387 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70720, d72387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d70720, d72387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d70721 q = 1) : d72388 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70721, d72388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d70721, d72388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d70722 q = 1) : d72389 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70722, d72389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d70722, d72389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro3082 (p : Pattern) (selected : d70729 p = 1) : d72396 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70715 q = 1) : d70715 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d70717 q = 1) : d72385 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70717, d72385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70717, d72385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3080 q selected
  have h3 (q : Pattern) (selected : d70718 q = 1) : d70718 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d70719 q = 1) : d72386 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70719, d72386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70719, d72386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d70727 q = 1) : d72394 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70727, d72394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70727, d72394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70728 q = 1) : d72395 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70728, d72395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70728, d72395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d70729 q = 1) : d72396 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70729, d72396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70729, d72396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro3083 (p : Pattern) (selected : d70740 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2430 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro172 q selected
    | true =>
      simp only [d2430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2431 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70738 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70739 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70740 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro3084 (p : Pattern) (selected : d70749 p = 1) : d72406 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70737 q = 1) : d70737 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d70741 q = 1) : d72402 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70741, d72402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70741, d72402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3083 q selected
  have h3 (q : Pattern) (selected : d70745 q = 1) : d70745 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d70746 q = 1) : d72403 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70746, d72403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70746, d72403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d70747 q = 1) : d72404 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70747, d72404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70747, d72404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70748 q = 1) : d72405 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70748, d72405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70748, d72405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d70749 q = 1) : d72406 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70749, d72406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70749, d72406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro3085 (p : Pattern) (selected : d70755 p = 1) : d72412 p = 1 := by
  have h0 (q : Pattern) (selected : d70685 q = 1) : d70685 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70723 q = 1) : d72390 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70723, d72390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3079 q selected
    | true =>
      simp only [d70723, d72390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3081 q selected
  have h2 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d70724 q = 1) : d72391 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70724, d72391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70724, d72391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d70725 q = 1) : d72392 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70725, d72392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70725, d72392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h5 (q : Pattern) (selected : d70726 q = 1) : d72393 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70726, d72393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70726, d72393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70730 q = 1) : d72397 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70730, d72397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70730, d72397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3082 q selected
  have h7 (q : Pattern) (selected : d70731 q = 1) : d72398 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70731, d72398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d70731, d72398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h8 (q : Pattern) (selected : d70732 q = 1) : d72399 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70732, d72399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d70732, d72399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h9 (q : Pattern) (selected : d70733 q = 1) : d72400 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70733, d72400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d70733, d72400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h10 (q : Pattern) (selected : d70734 q = 1) : d72401 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70734, d72401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d70734, d72401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d70750 q = 1) : d72407 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70750, d72407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70750, d72407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3084 q selected
  have h12 (q : Pattern) (selected : d70751 q = 1) : d72408 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70751, d72408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d70751, d72408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h13 (q : Pattern) (selected : d70752 q = 1) : d72409 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70752, d72409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d70752, d72409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h14 (q : Pattern) (selected : d70753 q = 1) : d72410 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70753, d72410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d70753, d72410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h15 (q : Pattern) (selected : d70754 q = 1) : d72411 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70754, d72411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d70754, d72411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h16 (q : Pattern) (selected : d70755 q = 1) : d72412 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d70755, d72412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d70755, d72412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro3086 (p : Pattern) (selected : d70761 p = 1) : d72418 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70756 q = 1) : d72413 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d70756, d72413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70756, d72413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3085 q selected
  have h2 (q : Pattern) (selected : d70757 q = 1) : d72414 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d70757, d72414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70757, d72414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d70758 q = 1) : d72415 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d70758, d72415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70758, d72415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d70759 q = 1) : d72416 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d70759, d72416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70759, d72416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d70760 q = 1) : d72417 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d70760, d72417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70760, d72417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70761 q = 1) : d72418 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d70761, d72418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70761, d72418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3087 (p : Pattern) (selected : d70767 p = 1) : d72424 p = 1 := by
  have h0 (q : Pattern) (selected : d70372 q = 1) : d72253 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d70372, d72253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3041 q selected
    | true =>
      simp only [d70372, d72253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3050 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d70468 q = 1) : d72293 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d70468, d72293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70468, d72293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3059 q selected
  have h3 (q : Pattern) (selected : d70469 q = 1) : d72294 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d70469, d72294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d70469, d72294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d70565 q = 1) : d72334 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d70565, d72334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70565, d72334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3068 q selected
  have h5 (q : Pattern) (selected : d70566 q = 1) : d72335 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d70566, d72335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70566, d72335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d70567 q = 1) : d72336 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d70567, d72336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70567, d72336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d70663 q = 1) : d72376 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d70663, d72376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70663, d72376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3077 q selected
  have h8 (q : Pattern) (selected : d70664 q = 1) : d72377 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d70664, d72377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70664, d72377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d70665 q = 1) : d72378 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d70665, d72378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70665, d72378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d70666 q = 1) : d72379 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d70666, d72379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d70666, d72379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d70762 q = 1) : d72419 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d70762, d72419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70762, d72419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3086 q selected
  have h12 (q : Pattern) (selected : d70763 q = 1) : d72420 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d70763, d72420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70763, d72420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d70764 q = 1) : d72421 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d70764, d72421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70764, d72421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d70765 q = 1) : d72422 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d70765, d72422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70765, d72422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d70766 q = 1) : d72423 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d70766, d72423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d70766, d72423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d70767 q = 1) : d72424 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d70767, d72424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d70767, d72424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro3088 (p : Pattern) (selected : d70773 p = 1) : d72430 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70768 q = 1) : d72425 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d70768, d72425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3087 q selected
    | true =>
      simp only [d70768, d72425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d70769 q = 1) : d72426 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d70769, d72426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70769, d72426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d70770 q = 1) : d72427 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d70770, d72427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70770, d72427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70771 q = 1) : d72428 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d70771, d72428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70771, d72428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70772 q = 1) : d72429 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d70772, d72429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70772, d72429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d70773 q = 1) : d72430 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d70773, d72430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d70773, d72430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3089 (p : Pattern) (selected : d70779 p = 1) : d72436 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70774 q = 1) : d72431 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d70774, d72431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3088 q selected
    | true =>
      simp only [d70774, d72431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d70775 q = 1) : d72432 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d70775, d72432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70775, d72432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d70776 q = 1) : d72433 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d70776, d72433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70776, d72433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70777 q = 1) : d72434 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d70777, d72434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70777, d72434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70778 q = 1) : d72435 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d70778, d72435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70778, d72435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d70779 q = 1) : d72436 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d70779, d72436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d70779, d72436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3090 (p : Pattern) (selected : d70785 p = 1) : d72442 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70780 q = 1) : d72437 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d70780, d72437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3089 q selected
    | true =>
      simp only [d70780, d72437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d70781 q = 1) : d72438 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d70781, d72438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70781, d72438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d70782 q = 1) : d72439 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d70782, d72439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70782, d72439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70783 q = 1) : d72440 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d70783, d72440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70783, d72440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70784 q = 1) : d72441 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d70784, d72441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70784, d72441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d70785 q = 1) : d72442 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d70785, d72442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d70785, d72442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3091 (p : Pattern) (selected : d70791 p = 1) : d72448 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70786 q = 1) : d72443 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d70786, d72443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3090 q selected
    | true =>
      simp only [d70786, d72443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d70787 q = 1) : d72444 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d70787, d72444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70787, d72444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d70788 q = 1) : d72445 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d70788, d72445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70788, d72445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70789 q = 1) : d72446 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d70789, d72446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70789, d72446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70790 q = 1) : d72447 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d70790, d72447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70790, d72447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d70791 q = 1) : d72448 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d70791, d72448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d70791, d72448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3092 (p : Pattern) (selected : d70797 p = 1) : d72454 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70792 q = 1) : d72449 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d70792, d72449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3091 q selected
    | true =>
      simp only [d70792, d72449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d70793 q = 1) : d72450 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d70793, d72450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70793, d72450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d70794 q = 1) : d72451 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d70794, d72451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70794, d72451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70795 q = 1) : d72452 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d70795, d72452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70795, d72452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70796 q = 1) : d72453 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d70796, d72453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70796, d72453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d70797 q = 1) : d72454 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d70797, d72454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d70797, d72454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3093 (p : Pattern) (selected : d70803 p = 1) : d72460 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70798 q = 1) : d72455 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d70798, d72455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3092 q selected
    | true =>
      simp only [d70798, d72455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d70799 q = 1) : d72456 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d70799, d72456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70799, d72456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d70800 q = 1) : d72457 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d70800, d72457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70800, d72457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70801 q = 1) : d72458 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d70801, d72458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70801, d72458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70802 q = 1) : d72459 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d70802, d72459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70802, d72459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d70803 q = 1) : d72460 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d70803, d72460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d70803, d72460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3094 (p : Pattern) (selected : d70809 p = 1) : d72466 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d70804 q = 1) : d72461 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d70804, d72461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3093 q selected
    | true =>
      simp only [d70804, d72461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d70805 q = 1) : d72462 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d70805, d72462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d70805, d72462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d70806 q = 1) : d72463 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d70806, d72463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d70806, d72463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d70807 q = 1) : d72464 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d70807, d72464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d70807, d72464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d70808 q = 1) : d72465 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d70808, d72465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d70808, d72465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d70809 q = 1) : d72466 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d70809, d72466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d70809, d72466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3095 (p : Pattern) (selected : d72611 p = 0) : d72768 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d72607 q = 0) : d72764 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72607, d72764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1259 q selected
    | true =>
      simp only [d72607, d72764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d72608 q = 0) : d72765 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72608, d72765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72608, d72765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d72609 q = 0) : d72766 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72609, d72766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72609, d72766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d72610 q = 0) : d72767 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72610, d72767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d72610, d72767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d72611 q = 0) : d72768 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d72611, d72768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d72611, d72768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro3096 (p : Pattern) (selected : d72622 p = 0) : d72779 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d72616 q = 0) : d72773 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72616, d72773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1262 q selected
    | true =>
      simp only [d72616, d72773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d72617 q = 0) : d72774 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72617, d72774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72617, d72774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d72618 q = 0) : d72775 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72618, d72775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1264 q selected
    | true =>
      simp only [d72618, d72775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d72619 q = 0) : d72776 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72619, d72776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d72619, d72776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d72620 q = 0) : d72777 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72620, d72777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d72620, d72777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d72621 q = 0) : d72778 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72621, d72778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d72621, d72778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d72622 q = 0) : d72779 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d72622, d72779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d72622, d72779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro3097 (p : Pattern) (selected : d72634 p = 0) : d72791 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d72628 q = 0) : d72785 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72628, d72785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1267 q selected
    | true =>
      simp only [d72628, d72785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d72629 q = 0) : d72786 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72629, d72786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72629, d72786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d72630 q = 0) : d72787 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72630, d72787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1269 q selected
    | true =>
      simp only [d72630, d72787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1262 q selected
  have h4 (q : Pattern) (selected : d72631 q = 0) : d72788 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72631, d72788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d72631, d72788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d72632 q = 0) : d72789 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72632, d72789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d72632, d72789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d72633 q = 0) : d72790 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72633, d72790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d72633, d72790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d72634 q = 0) : d72791 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d72634, d72791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d72634, d72791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro3098 (p : Pattern) (selected : d72640 p = 0) : d72797 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d72612 q = 0) : d72769 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d72612, d72769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72612, d72769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3095 q selected
  have h2 (q : Pattern) (selected : d72613 q = 0) : d72770 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d72613, d72770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72613, d72770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d72614 q = 0) : d72771 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d72614, d72771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72614, d72771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d72615 q = 0) : d72772 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d72615, d72772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72615, d72772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d72623 q = 0) : d72780 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d72623, d72780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72623, d72780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3096 q selected
  have h6 (q : Pattern) (selected : d72624 q = 0) : d72781 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d72624, d72781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72624, d72781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d72625 q = 0) : d72782 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d72625, d72782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72625, d72782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d72626 q = 0) : d72783 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d72626, d72783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72626, d72783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d72627 q = 0) : d72784 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d72627, d72784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d72627, d72784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d72635 q = 0) : d72792 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d72635, d72792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72635, d72792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3097 q selected
  have h11 (q : Pattern) (selected : d72636 q = 0) : d72793 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d72636, d72793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72636, d72793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d72637 q = 0) : d72794 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d72637, d72794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72637, d72794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d72638 q = 0) : d72795 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d72638, d72795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72638, d72795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d72639 q = 0) : d72796 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d72639, d72796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72639, d72796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d72640 q = 0) : d72797 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d72640, d72797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d72640, d72797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro3099 (p : Pattern) (selected : d72647 p = 0) : d72804 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d72641 q = 0) : d72798 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72641, d72798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1273 q selected
    | true =>
      simp only [d72641, d72798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d72642 q = 0) : d72799 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72642, d72799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72642, d72799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d72643 q = 0) : d72800 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72643, d72800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1275 q selected
    | true =>
      simp only [d72643, d72800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1277 q selected
  have h4 (q : Pattern) (selected : d72644 q = 0) : d72801 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72644, d72801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d72644, d72801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d72645 q = 0) : d72802 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72645, d72802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d72645, d72802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d72646 q = 0) : d72803 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72646, d72803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d72646, d72803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d72647 q = 0) : d72804 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d72647, d72804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d72647, d72804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro3100 (p : Pattern) (selected : d72653 p = 0) : d72810 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d72648 q = 0) : d72805 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d72648, d72805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72648, d72805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3099 q selected
  have h2 (q : Pattern) (selected : d72649 q = 0) : d72806 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d72649, d72806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72649, d72806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d72650 q = 0) : d72807 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d72650, d72807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72650, d72807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d72651 q = 0) : d72808 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d72651, d72808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72651, d72808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d72652 q = 0) : d72809 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d72652, d72809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72652, d72809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d72653 q = 0) : d72810 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d72653, d72810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72653, d72810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3101 (p : Pattern) (selected : d72661 p = 0) : d72818 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d72655 q = 0) : d72812 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72655, d72812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1281 q selected
    | true =>
      simp only [d72655, d72812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d72656 q = 0) : d72813 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72656, d72813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72656, d72813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d72657 q = 0) : d72814 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72657, d72814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1283 q selected
    | true =>
      simp only [d72657, d72814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1285 q selected
  have h4 (q : Pattern) (selected : d72658 q = 0) : d72815 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72658, d72815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d72658, d72815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d72659 q = 0) : d72816 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72659, d72816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d72659, d72816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d72660 q = 0) : d72817 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72660, d72817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d72660, d72817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d72661 q = 0) : d72818 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d72661, d72818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d72661, d72818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro3102 (p : Pattern) (selected : d72667 p = 0) : d72824 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d72662 q = 0) : d72819 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d72662, d72819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72662, d72819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3101 q selected
  have h2 (q : Pattern) (selected : d72663 q = 0) : d72820 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d72663, d72820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72663, d72820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d72664 q = 0) : d72821 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d72664, d72821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72664, d72821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d72665 q = 0) : d72822 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d72665, d72822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72665, d72822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d72666 q = 0) : d72823 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d72666, d72823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72666, d72823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d72667 q = 0) : d72824 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d72667, d72824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72667, d72824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3103 (p : Pattern) (selected : d72676 p = 0) : d72833 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d72670 q = 0) : d72827 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72670, d72827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1289 q selected
    | true =>
      simp only [d72670, d72827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d72671 q = 0) : d72828 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72671, d72828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72671, d72828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d72672 q = 0) : d72829 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72672, d72829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1291 q selected
    | true =>
      simp only [d72672, d72829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1293 q selected
  have h4 (q : Pattern) (selected : d72673 q = 0) : d72830 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72673, d72830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d72673, d72830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d72674 q = 0) : d72831 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72674, d72831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d72674, d72831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d72675 q = 0) : d72832 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72675, d72832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d72675, d72832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d72676 q = 0) : d72833 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d72676, d72833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d72676, d72833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro3104 (p : Pattern) (selected : d72682 p = 0) : d72839 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d72677 q = 0) : d72834 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d72677, d72834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72677, d72834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3103 q selected
  have h2 (q : Pattern) (selected : d72678 q = 0) : d72835 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d72678, d72835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72678, d72835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d72679 q = 0) : d72836 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d72679, d72836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72679, d72836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d72680 q = 0) : d72837 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d72680, d72837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72680, d72837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d72681 q = 0) : d72838 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d72681, d72838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72681, d72838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d72682 q = 0) : d72839 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d72682, d72839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72682, d72839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3105 (p : Pattern) (selected : d72692 p = 0) : d72849 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d72686 q = 0) : d72843 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72686, d72843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1297 q selected
    | true =>
      simp only [d72686, d72843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d72687 q = 0) : d72844 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72687, d72844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72687, d72844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d72688 q = 0) : d72845 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72688, d72845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1299 q selected
    | true =>
      simp only [d72688, d72845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1301 q selected
  have h4 (q : Pattern) (selected : d72689 q = 0) : d72846 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72689, d72846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d72689, d72846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d72690 q = 0) : d72847 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72690, d72847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d72690, d72847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d72691 q = 0) : d72848 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72691, d72848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d72691, d72848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d72692 q = 0) : d72849 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d72692, d72849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d72692, d72849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro3106 (p : Pattern) (selected : d72698 p = 0) : d72855 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d72693 q = 0) : d72850 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d72693, d72850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72693, d72850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3105 q selected
  have h2 (q : Pattern) (selected : d72694 q = 0) : d72851 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d72694, d72851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72694, d72851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d72695 q = 0) : d72852 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d72695, d72852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72695, d72852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d72696 q = 0) : d72853 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d72696, d72853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72696, d72853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d72697 q = 0) : d72854 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d72697, d72854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72697, d72854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d72698 q = 0) : d72855 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d72698, d72855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72698, d72855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3107 (p : Pattern) (selected : d72709 p = 0) : d72866 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d72703 q = 0) : d72860 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72703, d72860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1305 q selected
    | true =>
      simp only [d72703, d72860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d72704 q = 0) : d72861 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72704, d72861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72704, d72861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d72705 q = 0) : d72862 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72705, d72862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1307 q selected
    | true =>
      simp only [d72705, d72862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1309 q selected
  have h4 (q : Pattern) (selected : d72706 q = 0) : d72863 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72706, d72863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d72706, d72863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d72707 q = 0) : d72864 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72707, d72864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d72707, d72864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d72708 q = 0) : d72865 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72708, d72865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d72708, d72865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d72709 q = 0) : d72866 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d72709, d72866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d72709, d72866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro3108 (p : Pattern) (selected : d72715 p = 0) : d72872 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d72710 q = 0) : d72867 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d72710, d72867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72710, d72867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3107 q selected
  have h2 (q : Pattern) (selected : d72711 q = 0) : d72868 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d72711, d72868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72711, d72868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d72712 q = 0) : d72869 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d72712, d72869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72712, d72869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d72713 q = 0) : d72870 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d72713, d72870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72713, d72870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d72714 q = 0) : d72871 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d72714, d72871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72714, d72871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d72715 q = 0) : d72872 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d72715, d72872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72715, d72872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3109 (p : Pattern) (selected : d72721 p = 0) : d72878 p = 1 := by
  have h0 (q : Pattern) (selected : d72654 q = 0) : d72811 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d72654, d72811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3098 q selected
    | true =>
      simp only [d72654, d72811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3100 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d72668 q = 0) : d72825 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d72668, d72825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72668, d72825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3102 q selected
  have h3 (q : Pattern) (selected : d72669 q = 0) : d72826 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d72669, d72826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72669, d72826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d72683 q = 0) : d72840 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d72683, d72840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72683, d72840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3104 q selected
  have h5 (q : Pattern) (selected : d72684 q = 0) : d72841 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d72684, d72841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72684, d72841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d72685 q = 0) : d72842 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d72685, d72842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d72685, d72842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d72699 q = 0) : d72856 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d72699, d72856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72699, d72856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3106 q selected
  have h8 (q : Pattern) (selected : d72700 q = 0) : d72857 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d72700, d72857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72700, d72857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d72701 q = 0) : d72858 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d72701, d72858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72701, d72858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d72702 q = 0) : d72859 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d72702, d72859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d72702, d72859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d72716 q = 0) : d72873 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d72716, d72873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72716, d72873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3108 q selected
  have h12 (q : Pattern) (selected : d72717 q = 0) : d72874 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d72717, d72874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72717, d72874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d72718 q = 0) : d72875 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d72718, d72875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72718, d72875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d72719 q = 0) : d72876 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d72719, d72876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72719, d72876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d72720 q = 0) : d72877 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d72720, d72877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d72720, d72877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d72721 q = 0) : d72878 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d72721, d72878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d72721, d72878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro3110 (p : Pattern) (selected : d72727 p = 0) : d72884 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d72722 q = 0) : d72879 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d72722, d72879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3109 q selected
    | true =>
      simp only [d72722, d72879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d72723 q = 0) : d72880 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d72723, d72880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72723, d72880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d72724 q = 0) : d72881 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d72724, d72881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d72724, d72881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d72725 q = 0) : d72882 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d72725, d72882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d72725, d72882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d72726 q = 0) : d72883 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d72726, d72883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d72726, d72883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d72727 q = 0) : d72884 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d72727, d72884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d72727, d72884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3111 (p : Pattern) (selected : d72733 p = 0) : d72890 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d72728 q = 0) : d72885 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d72728, d72885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3110 q selected
    | true =>
      simp only [d72728, d72885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d72729 q = 0) : d72886 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d72729, d72886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72729, d72886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d72730 q = 0) : d72887 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d72730, d72887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d72730, d72887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d72731 q = 0) : d72888 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d72731, d72888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d72731, d72888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d72732 q = 0) : d72889 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d72732, d72889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d72732, d72889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d72733 q = 0) : d72890 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d72733, d72890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d72733, d72890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3112 (p : Pattern) (selected : d72739 p = 0) : d72896 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d72734 q = 0) : d72891 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d72734, d72891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3111 q selected
    | true =>
      simp only [d72734, d72891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d72735 q = 0) : d72892 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d72735, d72892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72735, d72892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d72736 q = 0) : d72893 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d72736, d72893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d72736, d72893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d72737 q = 0) : d72894 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d72737, d72894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d72737, d72894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d72738 q = 0) : d72895 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d72738, d72895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d72738, d72895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d72739 q = 0) : d72896 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d72739, d72896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d72739, d72896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3113 (p : Pattern) (selected : d72745 p = 0) : d72902 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d72740 q = 0) : d72897 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d72740, d72897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3112 q selected
    | true =>
      simp only [d72740, d72897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d72741 q = 0) : d72898 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d72741, d72898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72741, d72898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d72742 q = 0) : d72899 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d72742, d72899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d72742, d72899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d72743 q = 0) : d72900 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d72743, d72900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d72743, d72900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d72744 q = 0) : d72901 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d72744, d72901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d72744, d72901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d72745 q = 0) : d72902 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d72745, d72902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d72745, d72902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3114 (p : Pattern) (selected : d72751 p = 0) : d72908 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d72746 q = 0) : d72903 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d72746, d72903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3113 q selected
    | true =>
      simp only [d72746, d72903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d72747 q = 0) : d72904 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d72747, d72904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72747, d72904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d72748 q = 0) : d72905 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d72748, d72905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d72748, d72905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d72749 q = 0) : d72906 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d72749, d72906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d72749, d72906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d72750 q = 0) : d72907 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d72750, d72907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d72750, d72907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d72751 q = 0) : d72908 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d72751, d72908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d72751, d72908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3115 (p : Pattern) (selected : d72757 p = 0) : d72914 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d72752 q = 0) : d72909 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d72752, d72909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3114 q selected
    | true =>
      simp only [d72752, d72909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d72753 q = 0) : d72910 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d72753, d72910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72753, d72910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d72754 q = 0) : d72911 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d72754, d72911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d72754, d72911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d72755 q = 0) : d72912 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d72755, d72912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d72755, d72912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d72756 q = 0) : d72913 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d72756, d72913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d72756, d72913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d72757 q = 0) : d72914 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d72757, d72914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d72757, d72914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3116 (p : Pattern) (selected : d72763 p = 0) : d72920 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d72758 q = 0) : d72915 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d72758, d72915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3115 q selected
    | true =>
      simp only [d72758, d72915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d72759 q = 0) : d72916 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d72759, d72916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72759, d72916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d72760 q = 0) : d72917 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d72760, d72917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d72760, d72917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d72761 q = 0) : d72918 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d72761, d72918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d72761, d72918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d72762 q = 0) : d72919 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d72762, d72919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d72762, d72919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d72763 q = 0) : d72920 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d72763, d72920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d72763, d72920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3117 (p : Pattern) (selected : d72622 p = 1) : d73059 p = 1 := by
  have h0 (q : Pattern) (selected : d72617 q = 1) : d72617 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d72618 q = 1) : d73055 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72618, d73055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1321 q selected
    | true =>
      simp only [d72618, d73055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d72619 q = 1) : d73056 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72619, d73056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d72619, d73056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d72620 q = 1) : d73057 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72620, d73057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72620, d73057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d72621 q = 1) : d73058 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72621, d73058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d72621, d73058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d72622 q = 1) : d73059 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d72622, d73059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d72622, d73059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro3118 (p : Pattern) (selected : d72634 p = 1) : d73069 p = 1 := by
  have h0 (q : Pattern) (selected : d72629 q = 1) : d72629 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d103 q = 1) : d103 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d72630 q = 1) : d73065 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72630, d73065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1324 q selected
    | true =>
      simp only [d72630, d73065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d72631 q = 1) : d73066 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72631, d73066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d72631, d73066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d72632 q = 1) : d73067 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72632, d73067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72632, d73067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d72633 q = 1) : d73068 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72633, d73068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d72633, d73068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h7 (q : Pattern) (selected : d72634 q = 1) : d73069 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d72634, d73069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d72634, d73069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h7 p selected
theorem eqIntro3119 (p : Pattern) (selected : d72640 p = 1) : d73075 p = 1 := by
  have h0 (q : Pattern) (selected : d72615 q = 1) : d72615 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d72623 q = 1) : d73060 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d72623, d73060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72623, d73060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3117 q selected
  have h3 (q : Pattern) (selected : d72624 q = 1) : d73061 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d72624, d73061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72624, d73061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d72625 q = 1) : d73062 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d72625, d73062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72625, d73062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d72626 q = 1) : d73063 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d72626, d73063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72626, d73063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d72627 q = 1) : d73064 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d72627, d73064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72627, d73064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d72635 q = 1) : d73070 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d72635, d73070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72635, d73070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3118 q selected
  have h8 (q : Pattern) (selected : d72636 q = 1) : d73071 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d72636, d73071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72636, d73071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d72637 q = 1) : d73072 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d72637, d73072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72637, d73072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d72638 q = 1) : d73073 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d72638, d73073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72638, d73073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d72639 q = 1) : d73074 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d72639, d73074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72639, d73074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d72640 q = 1) : d73075 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d72640, d73075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d72640, d73075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro3120 (p : Pattern) (selected : d72647 p = 1) : d73080 p = 1 := by
  have h0 (q : Pattern) (selected : d72642 q = 1) : d72642 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d637 q = 1) : d637 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d72643 q = 1) : d73076 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72643, d73076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1328 q selected
    | true =>
      simp only [d72643, d73076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d72644 q = 1) : d73077 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72644, d73077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d72644, d73077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d72645 q = 1) : d73078 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72645, d73078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72645, d73078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d72646 q = 1) : d73079 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72646, d73079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d72646, d73079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h7 (q : Pattern) (selected : d72647 q = 1) : d73080 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d72647, d73080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d72647, d73080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h7 p selected
theorem eqIntro3121 (p : Pattern) (selected : d72653 p = 1) : d73086 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d72648 q = 1) : d73081 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d72648, d73081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72648, d73081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3120 q selected
  have h2 (q : Pattern) (selected : d72649 q = 1) : d73082 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d72649, d73082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72649, d73082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d72650 q = 1) : d73083 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d72650, d73083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72650, d73083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d72651 q = 1) : d73084 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d72651, d73084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72651, d73084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d72652 q = 1) : d73085 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d72652, d73085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72652, d73085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d72653 q = 1) : d73086 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d72653, d73086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72653, d73086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3122 (p : Pattern) (selected : d72661 p = 1) : d73092 p = 1 := by
  have h0 (q : Pattern) (selected : d72656 q = 1) : d72656 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d943 q = 1) : d943 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d72657 q = 1) : d73088 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72657, d73088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1332 q selected
    | true =>
      simp only [d72657, d73088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d72658 q = 1) : d73089 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72658, d73089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d72658, d73089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d72659 q = 1) : d73090 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72659, d73090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72659, d73090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d72660 q = 1) : d73091 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72660, d73091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d72660, d73091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h7 (q : Pattern) (selected : d72661 q = 1) : d73092 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d72661, d73092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d72661, d73092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h7 p selected
theorem eqIntro3123 (p : Pattern) (selected : d72667 p = 1) : d73098 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d72662 q = 1) : d73093 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d72662, d73093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72662, d73093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3122 q selected
  have h2 (q : Pattern) (selected : d72663 q = 1) : d73094 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d72663, d73094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72663, d73094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d72664 q = 1) : d73095 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d72664, d73095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72664, d73095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d72665 q = 1) : d73096 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d72665, d73096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72665, d73096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d72666 q = 1) : d73097 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d72666, d73097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72666, d73097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d72667 q = 1) : d73098 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d72667, d73098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72667, d73098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3124 (p : Pattern) (selected : d72676 p = 1) : d73105 p = 1 := by
  have h0 (q : Pattern) (selected : d72671 q = 1) : d72671 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1354 q = 1) : d1354 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d72672 q = 1) : d73101 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72672, d73101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1336 q selected
    | true =>
      simp only [d72672, d73101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d72673 q = 1) : d73102 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72673, d73102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d72673, d73102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d72674 q = 1) : d73103 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72674, d73103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72674, d73103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d72675 q = 1) : d73104 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72675, d73104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d72675, d73104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h7 (q : Pattern) (selected : d72676 q = 1) : d73105 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d72676, d73105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d72676, d73105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h7 p selected
theorem eqIntro3125 (p : Pattern) (selected : d72682 p = 1) : d73111 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d72677 q = 1) : d73106 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d72677, d73106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72677, d73106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3124 q selected
  have h2 (q : Pattern) (selected : d72678 q = 1) : d73107 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d72678, d73107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72678, d73107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d72679 q = 1) : d73108 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d72679, d73108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72679, d73108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d72680 q = 1) : d73109 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d72680, d73109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72680, d73109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d72681 q = 1) : d73110 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d72681, d73110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72681, d73110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d72682 q = 1) : d73111 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d72682, d73111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72682, d73111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3126 (p : Pattern) (selected : d72692 p = 1) : d73119 p = 1 := by
  have h0 (q : Pattern) (selected : d72687 q = 1) : d72687 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1831 q = 1) : d1831 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d72688 q = 1) : d73115 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72688, d73115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1340 q selected
    | true =>
      simp only [d72688, d73115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d72689 q = 1) : d73116 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72689, d73116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d72689, d73116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d72690 q = 1) : d73117 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72690, d73117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72690, d73117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d72691 q = 1) : d73118 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72691, d73118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d72691, d73118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h7 (q : Pattern) (selected : d72692 q = 1) : d73119 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d72692, d73119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d72692, d73119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h7 p selected
theorem eqIntro3127 (p : Pattern) (selected : d72698 p = 1) : d73125 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d72693 q = 1) : d73120 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d72693, d73120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72693, d73120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3126 q selected
  have h2 (q : Pattern) (selected : d72694 q = 1) : d73121 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d72694, d73121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72694, d73121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d72695 q = 1) : d73122 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d72695, d73122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72695, d73122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d72696 q = 1) : d73123 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d72696, d73123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72696, d73123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d72697 q = 1) : d73124 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d72697, d73124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72697, d73124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d72698 q = 1) : d73125 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d72698, d73125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72698, d73125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3128 (p : Pattern) (selected : d72709 p = 1) : d73134 p = 1 := by
  have h0 (q : Pattern) (selected : d72704 q = 1) : d72704 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2309 q = 1) : d2309 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d72705 q = 1) : d73130 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d72705, d73130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1344 q selected
    | true =>
      simp only [d72705, d73130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d72706 q = 1) : d73131 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d72706, d73131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d72706, d73131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d72707 q = 1) : d73132 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d72707, d73132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72707, d73132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d72708 q = 1) : d73133 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d72708, d73133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d72708, d73133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h7 (q : Pattern) (selected : d72709 q = 1) : d73134 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d72709, d73134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d72709, d73134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h7 p selected
theorem eqIntro3129 (p : Pattern) (selected : d72715 p = 1) : d73140 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d72710 q = 1) : d73135 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d72710, d73135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72710, d73135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3128 q selected
  have h2 (q : Pattern) (selected : d72711 q = 1) : d73136 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d72711, d73136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72711, d73136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d72712 q = 1) : d73137 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d72712, d73137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72712, d73137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d72713 q = 1) : d73138 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d72713, d73138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72713, d73138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d72714 q = 1) : d73139 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d72714, d73139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72714, d73139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d72715 q = 1) : d73140 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d72715, d73140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72715, d73140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3130 (p : Pattern) (selected : d72721 p = 1) : d73146 p = 1 := by
  have h0 (q : Pattern) (selected : d72654 q = 1) : d73087 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d72654, d73087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3119 q selected
    | true =>
      simp only [d72654, d73087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3121 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d72668 q = 1) : d73099 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d72668, d73099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72668, d73099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3123 q selected
  have h3 (q : Pattern) (selected : d72669 q = 1) : d73100 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d72669, d73100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d72669, d73100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d72683 q = 1) : d73112 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d72683, d73112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72683, d73112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3125 q selected
  have h5 (q : Pattern) (selected : d72684 q = 1) : d73113 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d72684, d73113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72684, d73113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d72685 q = 1) : d73114 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d72685, d73114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d72685, d73114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d72699 q = 1) : d73126 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d72699, d73126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72699, d73126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3127 q selected
  have h8 (q : Pattern) (selected : d72700 q = 1) : d73127 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d72700, d73127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72700, d73127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d72701 q = 1) : d73128 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d72701, d73128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72701, d73128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d72702 q = 1) : d73129 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d72702, d73129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d72702, d73129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d72716 q = 1) : d73141 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d72716, d73141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72716, d73141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3129 q selected
  have h12 (q : Pattern) (selected : d72717 q = 1) : d73142 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d72717, d73142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72717, d73142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d72718 q = 1) : d73143 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d72718, d73143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72718, d73143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d72719 q = 1) : d73144 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d72719, d73144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72719, d73144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d72720 q = 1) : d73145 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d72720, d73145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d72720, d73145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d72721 q = 1) : d73146 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d72721, d73146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d72721, d73146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro3131 (p : Pattern) (selected : d72727 p = 1) : d73152 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d72722 q = 1) : d73147 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d72722, d73147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3130 q selected
    | true =>
      simp only [d72722, d73147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d72723 q = 1) : d73148 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d72723, d73148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72723, d73148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d72724 q = 1) : d73149 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d72724, d73149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d72724, d73149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d72725 q = 1) : d73150 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d72725, d73150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d72725, d73150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d72726 q = 1) : d73151 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d72726, d73151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d72726, d73151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d72727 q = 1) : d73152 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d72727, d73152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d72727, d73152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3132 (p : Pattern) (selected : d72733 p = 1) : d73158 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d72728 q = 1) : d73153 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d72728, d73153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3131 q selected
    | true =>
      simp only [d72728, d73153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d72729 q = 1) : d73154 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d72729, d73154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72729, d73154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d72730 q = 1) : d73155 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d72730, d73155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d72730, d73155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d72731 q = 1) : d73156 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d72731, d73156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d72731, d73156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d72732 q = 1) : d73157 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d72732, d73157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d72732, d73157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d72733 q = 1) : d73158 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d72733, d73158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d72733, d73158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3133 (p : Pattern) (selected : d72739 p = 1) : d73164 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d72734 q = 1) : d73159 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d72734, d73159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3132 q selected
    | true =>
      simp only [d72734, d73159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d72735 q = 1) : d73160 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d72735, d73160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72735, d73160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d72736 q = 1) : d73161 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d72736, d73161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d72736, d73161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d72737 q = 1) : d73162 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d72737, d73162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d72737, d73162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d72738 q = 1) : d73163 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d72738, d73163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d72738, d73163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d72739 q = 1) : d73164 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d72739, d73164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d72739, d73164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3134 (p : Pattern) (selected : d72745 p = 1) : d73170 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d72740 q = 1) : d73165 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d72740, d73165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3133 q selected
    | true =>
      simp only [d72740, d73165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d72741 q = 1) : d73166 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d72741, d73166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72741, d73166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d72742 q = 1) : d73167 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d72742, d73167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d72742, d73167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d72743 q = 1) : d73168 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d72743, d73168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d72743, d73168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d72744 q = 1) : d73169 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d72744, d73169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d72744, d73169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d72745 q = 1) : d73170 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d72745, d73170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d72745, d73170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3135 (p : Pattern) (selected : d72751 p = 1) : d73176 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d72746 q = 1) : d73171 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d72746, d73171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3134 q selected
    | true =>
      simp only [d72746, d73171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d72747 q = 1) : d73172 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d72747, d73172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72747, d73172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d72748 q = 1) : d73173 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d72748, d73173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d72748, d73173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d72749 q = 1) : d73174 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d72749, d73174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d72749, d73174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d72750 q = 1) : d73175 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d72750, d73175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d72750, d73175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d72751 q = 1) : d73176 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d72751, d73176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d72751, d73176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3136 (p : Pattern) (selected : d72757 p = 1) : d73182 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d72752 q = 1) : d73177 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d72752, d73177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3135 q selected
    | true =>
      simp only [d72752, d73177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d72753 q = 1) : d73178 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d72753, d73178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72753, d73178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d72754 q = 1) : d73179 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d72754, d73179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d72754, d73179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d72755 q = 1) : d73180 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d72755, d73180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d72755, d73180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d72756 q = 1) : d73181 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d72756, d73181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d72756, d73181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d72757 q = 1) : d73182 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d72757, d73182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d72757, d73182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3137 (p : Pattern) (selected : d72763 p = 1) : d73188 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d72758 q = 1) : d73183 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d72758, d73183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3136 q selected
    | true =>
      simp only [d72758, d73183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d72759 q = 1) : d73184 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d72759, d73184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d72759, d73184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d72760 q = 1) : d73185 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d72760, d73185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d72760, d73185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d72761 q = 1) : d73186 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d72761, d73186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d72761, d73186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d72762 q = 1) : d73187 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d72762, d73187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d72762, d73187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d72763 q = 1) : d73188 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d72763, d73188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d72763, d73188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3138 (p : Pattern) (selected : d3324 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3319 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro649 q selected
    | true =>
      simp only [d3319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3320 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3321 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3322 q = 2) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3323 q = 2) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3324 q = 2) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3139 (p : Pattern) (selected : d3337 p = 2) : d61683 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3329 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro658 q selected
    | true =>
      simp only [d3329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3330 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3331 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3332 q = 2) : d3329 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3332, d3329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro672 q selected
    | true =>
      simp only [d3332, d3329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro678 q selected
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3333 q = 2) : d3330 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3333, d3330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3333, d3330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3334 q = 2) : d61680 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3334, d61680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3334, d61680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3335 q = 2) : d61681 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3335, d61681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3335, d61681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3336 q = 2) : d61682 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3336, d61682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3336, d61682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d3337 q = 2) : d61683 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3337, d61683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3337, d61683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro3140 (p : Pattern) (selected : d3352 p = 2) : d61692 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3343 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro688 q selected
    | true =>
      simp only [d3343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3344 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3345 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3346 q = 2) : d3343 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3346, d3343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro702 q selected
    | true =>
      simp only [d3346, d3343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3347 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro708 q selected
    | true =>
      simp only [d3347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3348 q = 2) : d3344 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3348, d3344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3348, d3344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3349 q = 2) : d61689 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3349, d61689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3349, d61689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3350 q = 2) : d61690 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3350, d61690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3350, d61690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3351 q = 2) : d61691 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3351, d61691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3351, d61691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d3352 q = 2) : d61692 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3352, d61692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3352, d61692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro3141 (p : Pattern) (selected : d3358 p = 2) : d61698 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3325 q = 2) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3138 q selected
  have h2 (q : Pattern) (selected : d3326 q = 2) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3327 q = 2) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3328 q = 2) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3338 q = 2) : d61684 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3338, d61684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3338, d61684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3139 q selected
  have h6 (q : Pattern) (selected : d3339 q = 2) : d61685 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3339, d61685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3339, d61685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3340 q = 2) : d61686 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3340, d61686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3340, d61686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d3341 q = 2) : d61687 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3341, d61687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3341, d61687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3342 q = 2) : d61688 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3342, d61688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3342, d61688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d3353 q = 2) : d61693 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3353, d61693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3353, d61693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3140 q selected
  have h11 (q : Pattern) (selected : d3354 q = 2) : d61694 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3354, d61694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3354, d61694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d3355 q = 2) : d61695 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3355, d61695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3355, d61695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d3356 q = 2) : d61696 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3356, d61696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3356, d61696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d3357 q = 2) : d61697 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3357, d61697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3357, d61697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d3358 q = 2) : d61698 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3358, d61698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3358, d61698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro3142 (p : Pattern) (selected : d3368 p = 2) : d61702 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3359 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro725 q selected
    | true =>
      simp only [d3359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3360 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3361 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3362 q = 2) : d3359 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3362, d3359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro746 q selected
    | true =>
      simp only [d3362, d3359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3363 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro755 q selected
    | true =>
      simp only [d3363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3364 q = 2) : d3360 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3364, d3360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3364, d3360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3365 q = 2) : d61699 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3365, d61699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3365, d61699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3366 q = 2) : d61700 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3366, d61700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3366, d61700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3367 q = 2) : d61701 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3367, d61701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3367, d61701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d3368 q = 2) : d61702 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3368, d61702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3368, d61702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro3143 (p : Pattern) (selected : d3374 p = 2) : d61708 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3369 q = 2) : d61703 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3369, d61703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3369, d61703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3142 q selected
  have h2 (q : Pattern) (selected : d3370 q = 2) : d61704 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3370, d61704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3370, d61704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3371 q = 2) : d61705 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3371, d61705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3371, d61705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3372 q = 2) : d61706 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3372, d61706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3372, d61706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3373 q = 2) : d61707 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3373, d61707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3373, d61707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3374 q = 2) : d61708 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3374, d61708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3374, d61708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3144 (p : Pattern) (selected : d3385 p = 2) : d61713 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3376 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro783 q selected
    | true =>
      simp only [d3376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3377 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3378 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3379 q = 2) : d3376 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3379, d3376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro808 q selected
    | true =>
      simp only [d3379, d3376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3380 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro817 q selected
    | true =>
      simp only [d3380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3381 q = 2) : d3377 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3381, d3377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3381, d3377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3382 q = 2) : d61710 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3382, d61710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3382, d61710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3383 q = 2) : d61711 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3383, d61711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3383, d61711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3384 q = 2) : d61712 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3384, d61712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3384, d61712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d3385 q = 2) : d61713 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3385, d61713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3385, d61713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro3145 (p : Pattern) (selected : d3391 p = 2) : d61719 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3386 q = 2) : d61714 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3386, d61714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3386, d61714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3144 q selected
  have h2 (q : Pattern) (selected : d3387 q = 2) : d61715 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3387, d61715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3387, d61715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3388 q = 2) : d61716 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3388, d61716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3388, d61716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3389 q = 2) : d61717 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3389, d61717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3389, d61717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3390 q = 2) : d61718 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3390, d61718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3390, d61718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3391 q = 2) : d61719 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3391, d61719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3391, d61719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3146 (p : Pattern) (selected : d3403 p = 2) : d61725 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3394 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro855 q selected
    | true =>
      simp only [d3394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3395 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3396 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3397 q = 2) : d3394 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3397, d3394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro884 q selected
    | true =>
      simp only [d3397, d3394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3398 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro893 q selected
    | true =>
      simp only [d3398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3399 q = 2) : d3395 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3399, d3395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3399, d3395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3400 q = 2) : d61722 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3400, d61722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3400, d61722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3401 q = 2) : d61723 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3401, d61723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3401, d61723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3402 q = 2) : d61724 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3402, d61724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3402, d61724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d3403 q = 2) : d61725 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3403, d61725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3403, d61725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro3147 (p : Pattern) (selected : d3409 p = 2) : d61731 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3404 q = 2) : d61726 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3404, d61726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3404, d61726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3146 q selected
  have h2 (q : Pattern) (selected : d3405 q = 2) : d61727 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3405, d61727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3405, d61727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3406 q = 2) : d61728 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3406, d61728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3406, d61728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3407 q = 2) : d61729 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3407, d61729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3407, d61729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3408 q = 2) : d61730 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3408, d61730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3408, d61730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3409 q = 2) : d61731 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3409, d61731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3409, d61731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3148 (p : Pattern) (selected : d3422 p = 2) : d61738 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3413 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro937 q selected
    | true =>
      simp only [d3413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3414 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3415 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3416 q = 2) : d3413 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3416, d3413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro970 q selected
    | true =>
      simp only [d3416, d3413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3417 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro979 q selected
    | true =>
      simp only [d3417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3418 q = 2) : d3414 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3418, d3414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3418, d3414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3419 q = 2) : d61735 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3419, d61735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3419, d61735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3420 q = 2) : d61736 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3420, d61736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3420, d61736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3421 q = 2) : d61737 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3421, d61737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3421, d61737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d3422 q = 2) : d61738 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3422, d61738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3422, d61738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro3149 (p : Pattern) (selected : d3428 p = 2) : d61744 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3423 q = 2) : d61739 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3423, d61739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3423, d61739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3148 q selected
  have h2 (q : Pattern) (selected : d3424 q = 2) : d61740 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3424, d61740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3424, d61740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3425 q = 2) : d61741 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3425, d61741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3425, d61741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3426 q = 2) : d61742 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3426, d61742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3426, d61742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3427 q = 2) : d61743 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3427, d61743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3427, d61743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3428 q = 2) : d61744 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3428, d61744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3428, d61744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3150 (p : Pattern) (selected : d3442 p = 2) : d61752 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3433 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1026 q selected
    | true =>
      simp only [d3433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3434 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3435 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3436 q = 2) : d3433 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3436, d3433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1060 q selected
    | true =>
      simp only [d3436, d3433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3437 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1069 q selected
    | true =>
      simp only [d3437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3438 q = 2) : d3434 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3438, d3434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3438, d3434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3439 q = 2) : d61749 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3439, d61749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3439, d61749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3440 q = 2) : d61750 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3440, d61750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3440, d61750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3441 q = 2) : d61751 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3441, d61751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3441, d61751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d3442 q = 2) : d61752 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3442, d61752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3442, d61752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro3151 (p : Pattern) (selected : d3448 p = 2) : d61758 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3443 q = 2) : d61753 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3443, d61753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3443, d61753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3150 q selected
  have h2 (q : Pattern) (selected : d3444 q = 2) : d61754 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3444, d61754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3444, d61754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3445 q = 2) : d61755 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3445, d61755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3445, d61755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3446 q = 2) : d61756 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3446, d61756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3446, d61756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3447 q = 2) : d61757 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3447, d61757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3447, d61757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3448 q = 2) : d61758 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3448, d61758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3448, d61758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3152 (p : Pattern) (selected : d3454 p = 2) : d61764 p = 1 := by
  have h0 (q : Pattern) (selected : d3375 q = 2) : d61709 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3375, d61709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3141 q selected
    | true =>
      simp only [d3375, d61709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3143 q selected
  have h1 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h2 (q : Pattern) (selected : d3392 q = 2) : d61720 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3392, d61720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3392, d61720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3145 q selected
  have h3 (q : Pattern) (selected : d3393 q = 2) : d61721 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3393, d61721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3393, d61721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3410 q = 2) : d61732 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3410, d61732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3410, d61732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3147 q selected
  have h5 (q : Pattern) (selected : d3411 q = 2) : d61733 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3411, d61733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3411, d61733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3412 q = 2) : d61734 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3412, d61734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3412, d61734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3429 q = 2) : d61745 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3429, d61745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3429, d61745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3149 q selected
  have h8 (q : Pattern) (selected : d3430 q = 2) : d61746 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3430, d61746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3430, d61746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3431 q = 2) : d61747 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3431, d61747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3431, d61747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d3432 q = 2) : d61748 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d3432, d61748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3432, d61748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d3449 q = 2) : d61759 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3449, d61759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3449, d61759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3151 q selected
  have h12 (q : Pattern) (selected : d3450 q = 2) : d61760 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3450, d61760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3450, d61760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d3451 q = 2) : d61761 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3451, d61761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3451, d61761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d3452 q = 2) : d61762 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d3452, d61762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3452, d61762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d3453 q = 2) : d61763 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d3453, d61763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d3453, d61763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d3454 q = 2) : d61764 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d3454, d61764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d3454, d61764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro3153 (p : Pattern) (selected : d3460 p = 2) : d61770 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3455 q = 2) : d61765 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d3455, d61765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3152 q selected
    | true =>
      simp only [d3455, d61765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3456 q = 2) : d61766 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d3456, d61766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3456, d61766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3457 q = 2) : d61767 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d3457, d61767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3457, d61767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3458 q = 2) : d61768 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d3458, d61768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3458, d61768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3459 q = 2) : d61769 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d3459, d61769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3459, d61769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3460 q = 2) : d61770 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d3460, d61770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3460, d61770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3154 (p : Pattern) (selected : d3466 p = 2) : d61776 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3461 q = 2) : d61771 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d3461, d61771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3153 q selected
    | true =>
      simp only [d3461, d61771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3462 q = 2) : d61772 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d3462, d61772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3462, d61772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3463 q = 2) : d61773 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d3463, d61773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3463, d61773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3464 q = 2) : d61774 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d3464, d61774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3464, d61774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3465 q = 2) : d61775 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d3465, d61775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3465, d61775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3466 q = 2) : d61776 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d3466, d61776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3466, d61776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3155 (p : Pattern) (selected : d3472 p = 2) : d61782 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3467 q = 2) : d61777 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d3467, d61777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3154 q selected
    | true =>
      simp only [d3467, d61777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3468 q = 2) : d61778 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d3468, d61778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3468, d61778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3469 q = 2) : d61779 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d3469, d61779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3469, d61779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3470 q = 2) : d61780 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d3470, d61780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3470, d61780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3471 q = 2) : d61781 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d3471, d61781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3471, d61781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3472 q = 2) : d61782 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d3472, d61782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3472, d61782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3156 (p : Pattern) (selected : d3478 p = 2) : d61788 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3473 q = 2) : d61783 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d3473, d61783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3155 q selected
    | true =>
      simp only [d3473, d61783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3474 q = 2) : d61784 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d3474, d61784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3474, d61784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3475 q = 2) : d61785 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d3475, d61785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3475, d61785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3476 q = 2) : d61786 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d3476, d61786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3476, d61786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3477 q = 2) : d61787 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d3477, d61787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3477, d61787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3478 q = 2) : d61788 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d3478, d61788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3478, d61788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3157 (p : Pattern) (selected : d3484 p = 2) : d61794 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3479 q = 2) : d61789 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d3479, d61789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3156 q selected
    | true =>
      simp only [d3479, d61789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3480 q = 2) : d61790 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d3480, d61790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3480, d61790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3481 q = 2) : d61791 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d3481, d61791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3481, d61791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3482 q = 2) : d61792 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d3482, d61792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3482, d61792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3483 q = 2) : d61793 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d3483, d61793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3483, d61793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3484 q = 2) : d61794 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d3484, d61794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3484, d61794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3158 (p : Pattern) (selected : d3490 p = 2) : d61800 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3485 q = 2) : d61795 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d3485, d61795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3157 q selected
    | true =>
      simp only [d3485, d61795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3486 q = 2) : d61796 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d3486, d61796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3486, d61796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3487 q = 2) : d61797 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d3487, d61797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3487, d61797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3488 q = 2) : d61798 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d3488, d61798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3488, d61798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3489 q = 2) : d61799 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d3489, d61799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3489, d61799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3490 q = 2) : d61800 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d3490, d61800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3490, d61800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3159 (p : Pattern) (selected : d3496 p = 2) : d61806 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3491 q = 2) : d61801 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d3491, d61801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3158 q selected
    | true =>
      simp only [d3491, d61801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3492 q = 2) : d61802 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d3492, d61802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3492, d61802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3493 q = 2) : d61803 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d3493, d61803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3493, d61803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3494 q = 2) : d61804 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d3494, d61804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3494, d61804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3495 q = 2) : d61805 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d3495, d61805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3495, d61805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3496 q = 2) : d61806 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d3496, d61806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3496, d61806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3160 (p : Pattern) (selected : d3497 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d43 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro648 q selected
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d45 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d47 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3497 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3161 (p : Pattern) (selected : d3503 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3498 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3160 q selected
  have h2 (q : Pattern) (selected : d3499 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3500 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3501 q = 2) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3502 q = 2) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3503 q = 2) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3162 (p : Pattern) (selected : d3509 p = 2) : d213 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d117 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro660 q selected
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d119 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d120 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d124 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro661 q selected
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d125 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d126 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d157 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro666 q selected
    | true =>
      simp only [d157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro648 q selected
  have h9 (q : Pattern) (selected : d188 q = 2) : d43 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188, d43, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro671 q selected
    | true =>
      simp only [d188, d43, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d189 q = 2) : d100 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189, d100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d189, d100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d43 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro648 q selected
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d44 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d190 q = 2) : d101 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d190, d101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d190, d101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d191 q = 2) : d102 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d191, d102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d191, d102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d192 q = 2) : d103 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192, d103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d192, d103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d3509 q = 2) : d213 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3509, d213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d3509, d213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro3163 (p : Pattern) (selected : d3515 p = 2) : d62704 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2525 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro678 q selected
  have h2 (q : Pattern) (selected : d2526 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3508 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3510 q = 2) : d2525 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3510, d2525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3510, d2525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3162 q selected
  have h5 (q : Pattern) (selected : d214 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro678 q selected
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3511 q = 2) : d2526 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3511, d2526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3511, d2526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3512 q = 2) : d2527 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3512, d2527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3512, d2527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3513 q = 2) : d62702 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3513, d62702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3513, d62702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3514 q = 2) : d62703 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3514, d62703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3514, d62703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d3515 q = 2) : d62704 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3515, d62704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3515, d62704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro3164 (p : Pattern) (selected : d3522 p = 2) : d2536 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d297 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro690 q selected
    | true =>
      simp only [d297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro660 q selected
  have h2 (q : Pattern) (selected : d298 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d299 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d300 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d304 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro691 q selected
    | true =>
      simp only [d304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro661 q selected
  have h6 (q : Pattern) (selected : d305 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d306 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d337 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro696 q selected
    | true =>
      simp only [d337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro666 q selected
  have h9 (q : Pattern) (selected : d368 q = 2) : d157 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368, d157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro701 q selected
    | true =>
      simp only [d368, d157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro671 q selected
  have h10 (q : Pattern) (selected : d369 q = 2) : d280 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d369, d280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d369, d280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d370 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro666 q selected
    | true =>
      simp only [d370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d371 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d372 q = 2) : d281 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d372, d281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d372, d281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d373 q = 2) : d282 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d373, d282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d373, d282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d374 q = 2) : d283 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d374, d283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d374, d283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d3522 q = 2) : d2536 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3522, d2536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d3522, d2536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro3165 (p : Pattern) (selected : d3529 p = 2) : d62712 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2537 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1212 q selected
  have h2 (q : Pattern) (selected : d2538 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3521 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3523 q = 2) : d2537 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3523, d2537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3523, d2537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3164 q selected
  have h5 (q : Pattern) (selected : d3524 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1212 q selected
    | true =>
      simp only [d3524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro678 q selected
  have h6 (q : Pattern) (selected : d3525 q = 2) : d2538 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3525, d2538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3525, d2538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3526 q = 2) : d2539 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3526, d2539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3526, d2539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3527 q = 2) : d62710 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3527, d62710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3527, d62710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3528 q = 2) : d62711 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3528, d62711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3528, d62711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d3529 q = 2) : d62712 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3529, d62712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3529, d62712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro3166 (p : Pattern) (selected : d3535 p = 2) : d62718 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3504 q = 2) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3161 q selected
  have h2 (q : Pattern) (selected : d3505 q = 2) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3506 q = 2) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3507 q = 2) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3516 q = 2) : d62705 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3516, d62705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3516, d62705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3163 q selected
  have h6 (q : Pattern) (selected : d3517 q = 2) : d62706 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3517, d62706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3517, d62706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3518 q = 2) : d62707 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3518, d62707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3518, d62707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d3519 q = 2) : d62708 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3519, d62708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3519, d62708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3520 q = 2) : d62709 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3520, d62709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3520, d62709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d3530 q = 2) : d62713 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3530, d62713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3530, d62713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3165 q selected
  have h11 (q : Pattern) (selected : d3531 q = 2) : d62714 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3531, d62714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3531, d62714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d3532 q = 2) : d62715 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3532, d62715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3532, d62715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d3533 q = 2) : d62716 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3533, d62716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3533, d62716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d3534 q = 2) : d62717 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3534, d62717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3534, d62717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d3535 q = 2) : d62718 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3535, d62718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3535, d62718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro3167 (p : Pattern) (selected : d3537 p = 2) : d2549 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d515 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro729 q selected
    | true =>
      simp only [d515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro730 q selected
  have h2 (q : Pattern) (selected : d516 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d517 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d518 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d525 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro731 q selected
    | true =>
      simp only [d525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro732 q selected
  have h6 (q : Pattern) (selected : d526 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d527 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d561 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro738 q selected
    | true =>
      simp only [d561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro723 q selected
  have h9 (q : Pattern) (selected : d601 q = 2) : d492 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d601, d492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro744 q selected
    | true =>
      simp only [d601, d492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro745 q selected
  have h10 (q : Pattern) (selected : d602 q = 2) : d493 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d602, d493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d602, d493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d603 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro723 q selected
    | true =>
      simp only [d603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d604 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d605 q = 2) : d494 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d605, d494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d605, d494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d606 q = 2) : d495 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d606, d495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d606, d495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d607 q = 2) : d496 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d607, d496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d607, d496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d3537 q = 2) : d2549 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3537, d2549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d3537, d2549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro3168 (p : Pattern) (selected : d3539 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d633 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro724 q selected
    | true =>
      simp only [d633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d634 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d635 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d636 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d637 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3539 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3169 (p : Pattern) (selected : d3545 p = 2) : d62721 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2550 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1215 q selected
  have h2 (q : Pattern) (selected : d2551 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3536 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3538 q = 2) : d2550 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3538, d2550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3538, d2550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3167 q selected
  have h5 (q : Pattern) (selected : d3540 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1215 q selected
    | true =>
      simp only [d3540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3168 q selected
  have h6 (q : Pattern) (selected : d3541 q = 2) : d2551 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3541, d2551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3541, d2551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3542 q = 2) : d2552 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3542, d2552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3542, d2552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3543 q = 2) : d62719 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3543, d62719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3543, d62719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3544 q = 2) : d62720 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3544, d62720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3544, d62720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d3545 q = 2) : d62721 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3545, d62721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3545, d62721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro3170 (p : Pattern) (selected : d3551 p = 2) : d62727 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3546 q = 2) : d62722 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3546, d62722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3546, d62722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3169 q selected
  have h2 (q : Pattern) (selected : d3547 q = 2) : d62723 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3547, d62723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3547, d62723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3548 q = 2) : d62724 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3548, d62724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3548, d62724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3549 q = 2) : d62725 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3549, d62725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3549, d62725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3550 q = 2) : d62726 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3550, d62726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3550, d62726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3551 q = 2) : d62727 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3551, d62727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3551, d62727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3171 (p : Pattern) (selected : d3554 p = 2) : d2563 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d807 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro787 q selected
    | true =>
      simp only [d807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro788 q selected
  have h2 (q : Pattern) (selected : d808 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d809 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d810 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d817 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro789 q selected
    | true =>
      simp only [d817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro790 q selected
  have h6 (q : Pattern) (selected : d818 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d819 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d852 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro796 q selected
    | true =>
      simp only [d852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro781 q selected
  have h9 (q : Pattern) (selected : d907 q = 2) : d784 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d907, d784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro806 q selected
    | true =>
      simp only [d907, d784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro807 q selected
  have h10 (q : Pattern) (selected : d908 q = 2) : d785 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d908, d785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d908, d785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d909 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro781 q selected
    | true =>
      simp only [d909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d910 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d911 q = 2) : d786 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d911, d786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d911, d786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d912 q = 2) : d787 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d912, d787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d912, d787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d913 q = 2) : d788 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d913, d788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d913, d788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d3554 q = 2) : d2563 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3554, d2563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d3554, d2563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro3172 (p : Pattern) (selected : d3556 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d939 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro782 q selected
    | true =>
      simp only [d939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d940 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d941 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d942 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d943 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3556 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3173 (p : Pattern) (selected : d3562 p = 2) : d62731 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2564 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1218 q selected
  have h2 (q : Pattern) (selected : d2565 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3553 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3555 q = 2) : d2564 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3555, d2564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3555, d2564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3171 q selected
  have h5 (q : Pattern) (selected : d3557 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1218 q selected
    | true =>
      simp only [d3557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3172 q selected
  have h6 (q : Pattern) (selected : d3558 q = 2) : d2565 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3558, d2565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3558, d2565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3559 q = 2) : d2566 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3559, d2566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3559, d2566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3560 q = 2) : d62729 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3560, d62729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3560, d62729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3561 q = 2) : d62730 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3561, d62730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3561, d62730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d3562 q = 2) : d62731 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3562, d62731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3562, d62731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro3174 (p : Pattern) (selected : d3568 p = 2) : d62737 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3563 q = 2) : d62732 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3563, d62732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3563, d62732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3173 q selected
  have h2 (q : Pattern) (selected : d3564 q = 2) : d62733 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3564, d62733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3564, d62733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3565 q = 2) : d62734 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3565, d62734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3565, d62734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3566 q = 2) : d62735 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3566, d62735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3566, d62735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3567 q = 2) : d62736 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3567, d62736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3567, d62736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3568 q = 2) : d62737 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3568, d62737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3568, d62737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3175 (p : Pattern) (selected : d3572 p = 2) : d2578 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1186 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro859 q selected
    | true =>
      simp only [d1186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro860 q selected
  have h2 (q : Pattern) (selected : d1187 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1188 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1189 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1196 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro861 q selected
    | true =>
      simp only [d1196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro862 q selected
  have h6 (q : Pattern) (selected : d1197 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1198 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d1228 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro868 q selected
    | true =>
      simp only [d1228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro853 q selected
  have h9 (q : Pattern) (selected : d1318 q = 2) : d1163 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1318, d1163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro882 q selected
    | true =>
      simp only [d1318, d1163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro883 q selected
  have h10 (q : Pattern) (selected : d1319 q = 2) : d1164 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1319, d1164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1319, d1164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d1320 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro853 q selected
    | true =>
      simp only [d1320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d1321 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d1321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d1322 q = 2) : d1165 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1322, d1165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d1322, d1165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d1323 q = 2) : d1166 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1323, d1166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1323, d1166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d1324 q = 2) : d1167 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1324, d1167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1324, d1167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d3572 q = 2) : d2578 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3572, d2578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d3572, d2578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro3176 (p : Pattern) (selected : d3574 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1350 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro854 q selected
    | true =>
      simp only [d1350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1351 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1352 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1353 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1354 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3574 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3177 (p : Pattern) (selected : d3580 p = 2) : d62742 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2579 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1221 q selected
  have h2 (q : Pattern) (selected : d2580 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3571 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3573 q = 2) : d2579 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3573, d2579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3573, d2579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3175 q selected
  have h5 (q : Pattern) (selected : d3575 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1221 q selected
    | true =>
      simp only [d3575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3176 q selected
  have h6 (q : Pattern) (selected : d3576 q = 2) : d2580 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3576, d2580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3576, d2580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3577 q = 2) : d2581 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3577, d2581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3577, d2581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3578 q = 2) : d62740 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3578, d62740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3578, d62740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3579 q = 2) : d62741 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3579, d62741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3579, d62741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d3580 q = 2) : d62742 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3580, d62742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3580, d62742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro3178 (p : Pattern) (selected : d3586 p = 2) : d62748 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3581 q = 2) : d62743 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3581, d62743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3581, d62743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3177 q selected
  have h2 (q : Pattern) (selected : d3582 q = 2) : d62744 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3582, d62744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3582, d62744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3583 q = 2) : d62745 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3583, d62745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3583, d62745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3584 q = 2) : d62746 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3584, d62746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3584, d62746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3585 q = 2) : d62747 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3585, d62747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3585, d62747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3586 q = 2) : d62748 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3586, d62748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3586, d62748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3179 (p : Pattern) (selected : d3591 p = 2) : d2594 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1647 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro941 q selected
    | true =>
      simp only [d1647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro942 q selected
  have h2 (q : Pattern) (selected : d1648 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1649 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1650 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1657 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro943 q selected
    | true =>
      simp only [d1657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro944 q selected
  have h6 (q : Pattern) (selected : d1658 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1659 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d1683 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro948 q selected
    | true =>
      simp only [d1683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro935 q selected
  have h9 (q : Pattern) (selected : d1795 q = 2) : d1624 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1795, d1624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro968 q selected
    | true =>
      simp only [d1795, d1624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro969 q selected
  have h10 (q : Pattern) (selected : d1796 q = 2) : d1625 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1796, d1625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1796, d1625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d1797 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro935 q selected
    | true =>
      simp only [d1797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d1798 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d1798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d1799 q = 2) : d1626 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1799, d1626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d1799, d1626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d1800 q = 2) : d1627 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1800, d1627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1800, d1627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d1801 q = 2) : d1628 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1801, d1628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1801, d1628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d3591 q = 2) : d2594 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3591, d2594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d3591, d2594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro3180 (p : Pattern) (selected : d3593 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1827 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro936 q selected
    | true =>
      simp only [d1827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1828 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1829 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1830 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1831 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3593 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3181 (p : Pattern) (selected : d3599 p = 2) : d62754 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2595 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1224 q selected
  have h2 (q : Pattern) (selected : d2596 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3590 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3592 q = 2) : d2595 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3592, d2595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3592, d2595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3179 q selected
  have h5 (q : Pattern) (selected : d3594 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1224 q selected
    | true =>
      simp only [d3594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3180 q selected
  have h6 (q : Pattern) (selected : d3595 q = 2) : d2596 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3595, d2596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3595, d2596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3596 q = 2) : d2597 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3596, d2597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3596, d2597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3597 q = 2) : d62752 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3597, d62752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3597, d62752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3598 q = 2) : d62753 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3598, d62753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3598, d62753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d3599 q = 2) : d62754 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3599, d62754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3599, d62754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro3182 (p : Pattern) (selected : d3605 p = 2) : d62760 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3600 q = 2) : d62755 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3600, d62755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3600, d62755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3181 q selected
  have h2 (q : Pattern) (selected : d3601 q = 2) : d62756 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3601, d62756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3601, d62756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3602 q = 2) : d62757 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3602, d62757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3602, d62757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3603 q = 2) : d62758 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3603, d62758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3603, d62758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3604 q = 2) : d62759 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3604, d62759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3604, d62759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3605 q = 2) : d62760 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3605, d62760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3605, d62760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3183 (p : Pattern) (selected : d3611 p = 2) : d2611 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2130 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1030 q selected
    | true =>
      simp only [d2130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1031 q selected
  have h2 (q : Pattern) (selected : d2131 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2132 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2133 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2140 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1032 q selected
    | true =>
      simp only [d2140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1033 q selected
  have h6 (q : Pattern) (selected : d2141 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2142 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d2162 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1037 q selected
    | true =>
      simp only [d2162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1024 q selected
  have h9 (q : Pattern) (selected : d2273 q = 2) : d2107 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2273, d2107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1058 q selected
    | true =>
      simp only [d2273, d2107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1059 q selected
  have h10 (q : Pattern) (selected : d2274 q = 2) : d2108 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2274, d2108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d2274, d2108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d2275 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1024 q selected
    | true =>
      simp only [d2275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d2276 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d2276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d2277 q = 2) : d2109 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2277, d2109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d2277, d2109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d2278 q = 2) : d2110 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2278, d2110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2278, d2110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d2279 q = 2) : d2111 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2279, d2111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2279, d2111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d3611 q = 2) : d2611 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3611, d2611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d3611, d2611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro3184 (p : Pattern) (selected : d3613 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2305 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1025 q selected
    | true =>
      simp only [d2305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2306 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2307 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2308 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2309 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3613 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3185 (p : Pattern) (selected : d3619 p = 2) : d62767 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2612 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1227 q selected
  have h2 (q : Pattern) (selected : d2613 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3610 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3612 q = 2) : d2612 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3612, d2612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3612, d2612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3183 q selected
  have h5 (q : Pattern) (selected : d3614 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1227 q selected
    | true =>
      simp only [d3614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3184 q selected
  have h6 (q : Pattern) (selected : d3615 q = 2) : d2613 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3615, d2613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3615, d2613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3616 q = 2) : d2614 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3616, d2614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3616, d2614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3617 q = 2) : d62765 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3617, d62765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3617, d62765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3618 q = 2) : d62766 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3618, d62766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3618, d62766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d3619 q = 2) : d62767 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3619, d62767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3619, d62767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro3186 (p : Pattern) (selected : d3625 p = 2) : d62773 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3620 q = 2) : d62768 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3620, d62768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3620, d62768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3185 q selected
  have h2 (q : Pattern) (selected : d3621 q = 2) : d62769 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3621, d62769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3621, d62769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3622 q = 2) : d62770 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3622, d62770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3622, d62770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3623 q = 2) : d62771 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3623, d62771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3623, d62771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3624 q = 2) : d62772 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3624, d62772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3624, d62772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3625 q = 2) : d62773 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3625, d62773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3625, d62773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3187 (p : Pattern) (selected : d3631 p = 2) : d62779 p = 1 := by
  have h0 (q : Pattern) (selected : d3552 q = 2) : d62728 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3552, d62728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3166 q selected
    | true =>
      simp only [d3552, d62728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3170 q selected
  have h1 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h2 (q : Pattern) (selected : d3569 q = 2) : d62738 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3569, d62738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3569, d62738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3174 q selected
  have h3 (q : Pattern) (selected : d3570 q = 2) : d62739 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3570, d62739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3570, d62739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3587 q = 2) : d62749 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3587, d62749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3587, d62749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3178 q selected
  have h5 (q : Pattern) (selected : d3588 q = 2) : d62750 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3588, d62750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3588, d62750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3589 q = 2) : d62751 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3589, d62751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3589, d62751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3606 q = 2) : d62761 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3606, d62761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3606, d62761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3182 q selected
  have h8 (q : Pattern) (selected : d3607 q = 2) : d62762 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3607, d62762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3607, d62762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3608 q = 2) : d62763 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3608, d62763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3608, d62763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d3609 q = 2) : d62764 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d3609, d62764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3609, d62764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d3626 q = 2) : d62774 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3626, d62774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3626, d62774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3186 q selected
  have h12 (q : Pattern) (selected : d3627 q = 2) : d62775 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3627, d62775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3627, d62775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d3628 q = 2) : d62776 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3628, d62776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3628, d62776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d3629 q = 2) : d62777 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d3629, d62777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3629, d62777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d3630 q = 2) : d62778 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d3630, d62778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d3630, d62778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d3631 q = 2) : d62779 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d3631, d62779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d3631, d62779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro3188 (p : Pattern) (selected : d3637 p = 2) : d62785 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3632 q = 2) : d62780 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d3632, d62780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3187 q selected
    | true =>
      simp only [d3632, d62780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3633 q = 2) : d62781 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d3633, d62781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3633, d62781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3634 q = 2) : d62782 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d3634, d62782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3634, d62782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3635 q = 2) : d62783 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d3635, d62783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3635, d62783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3636 q = 2) : d62784 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d3636, d62784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3636, d62784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3637 q = 2) : d62785 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d3637, d62785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3637, d62785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3189 (p : Pattern) (selected : d3643 p = 2) : d62791 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3638 q = 2) : d62786 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d3638, d62786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3188 q selected
    | true =>
      simp only [d3638, d62786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3639 q = 2) : d62787 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d3639, d62787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3639, d62787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3640 q = 2) : d62788 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d3640, d62788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3640, d62788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3641 q = 2) : d62789 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d3641, d62789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3641, d62789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3642 q = 2) : d62790 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d3642, d62790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3642, d62790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3643 q = 2) : d62791 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d3643, d62791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3643, d62791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3190 (p : Pattern) (selected : d3649 p = 2) : d62797 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3644 q = 2) : d62792 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d3644, d62792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3189 q selected
    | true =>
      simp only [d3644, d62792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3645 q = 2) : d62793 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d3645, d62793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3645, d62793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3646 q = 2) : d62794 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d3646, d62794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3646, d62794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3647 q = 2) : d62795 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d3647, d62795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3647, d62795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3648 q = 2) : d62796 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d3648, d62796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3648, d62796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3649 q = 2) : d62797 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d3649, d62797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3649, d62797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3191 (p : Pattern) (selected : d3655 p = 2) : d62803 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3650 q = 2) : d62798 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d3650, d62798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3190 q selected
    | true =>
      simp only [d3650, d62798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3651 q = 2) : d62799 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d3651, d62799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3651, d62799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3652 q = 2) : d62800 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d3652, d62800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3652, d62800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3653 q = 2) : d62801 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d3653, d62801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3653, d62801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3654 q = 2) : d62802 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d3654, d62802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3654, d62802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3655 q = 2) : d62803 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d3655, d62803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3655, d62803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3192 (p : Pattern) (selected : d3661 p = 2) : d62809 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3656 q = 2) : d62804 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d3656, d62804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3191 q selected
    | true =>
      simp only [d3656, d62804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3657 q = 2) : d62805 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d3657, d62805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3657, d62805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3658 q = 2) : d62806 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d3658, d62806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3658, d62806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3659 q = 2) : d62807 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d3659, d62807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3659, d62807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3660 q = 2) : d62808 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d3660, d62808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3660, d62808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3661 q = 2) : d62809 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d3661, d62809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3661, d62809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3193 (p : Pattern) (selected : d3667 p = 2) : d62815 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3662 q = 2) : d62810 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d3662, d62810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3192 q selected
    | true =>
      simp only [d3662, d62810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3663 q = 2) : d62811 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d3663, d62811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3663, d62811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3664 q = 2) : d62812 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d3664, d62812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3664, d62812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3665 q = 2) : d62813 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d3665, d62813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3665, d62813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3666 q = 2) : d62814 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d3666, d62814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3666, d62814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3667 q = 2) : d62815 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d3667, d62815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3667, d62815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3194 (p : Pattern) (selected : d3673 p = 2) : d62821 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3668 q = 2) : d62816 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d3668, d62816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3193 q selected
    | true =>
      simp only [d3668, d62816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3669 q = 2) : d62817 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d3669, d62817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3669, d62817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3670 q = 2) : d62818 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d3670, d62818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3670, d62818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3671 q = 2) : d62819 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d3671, d62819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3671, d62819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3672 q = 2) : d62820 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d3672, d62820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3672, d62820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3673 q = 2) : d62821 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d3673, d62821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3673, d62821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3195 (p : Pattern) (selected : d73786 p = 0) : d73913 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d73783 q = 0) : d73910 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d73783, d73910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro220 q selected
    | true =>
      simp only [d73783, d73910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d73784 q = 0) : d73911 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d73784, d73911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73784, d73911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d73785 q = 0) : d73912 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d73785, d73912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d73785, d73912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d73786 q = 0) : d73913 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d73786, d73913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d73786, d73913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro3196 (p : Pattern) (selected : d73795 p = 0) : d73922 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d73792 q = 0) : d73919 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d73792, d73919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro250 q selected
    | true =>
      simp only [d73792, d73919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d73793 q = 0) : d73920 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d73793, d73920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73793, d73920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d73794 q = 0) : d73921 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d73794, d73921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d73794, d73921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d73795 q = 0) : d73922 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d73795, d73922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d73795, d73922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro3197 (p : Pattern) (selected : d73801 p = 0) : d73928 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d73787 q = 0) : d73914 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d73787, d73914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73787, d73914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3195 q selected
  have h2 (q : Pattern) (selected : d73788 q = 0) : d73915 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d73788, d73915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73788, d73915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d73789 q = 0) : d73916 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d73789, d73916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73789, d73916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d73790 q = 0) : d73917 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d73790, d73917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73790, d73917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d73791 q = 0) : d73918 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d73791, d73918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73791, d73918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d73796 q = 0) : d73923 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d73796, d73923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73796, d73923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3196 q selected
  have h7 (q : Pattern) (selected : d73797 q = 0) : d73924 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d73797, d73924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73797, d73924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d73798 q = 0) : d73925 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d73798, d73925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73798, d73925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d73799 q = 0) : d73926 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d73799, d73926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73799, d73926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d73800 q = 0) : d73927 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d73800, d73927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73800, d73927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d73801 q = 0) : d73928 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d73801, d73928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d73801, d73928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro3198 (p : Pattern) (selected : d73805 p = 0) : d73932 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d73802 q = 0) : d73929 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d73802, d73929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro297 q selected
    | true =>
      simp only [d73802, d73929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d73803 q = 0) : d73930 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d73803, d73930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73803, d73930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d73804 q = 0) : d73931 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d73804, d73931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d73804, d73931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d73805 q = 0) : d73932 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d73805, d73932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d73805, d73932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro3199 (p : Pattern) (selected : d73811 p = 0) : d73938 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d73806 q = 0) : d73933 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d73806, d73933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73806, d73933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3198 q selected
  have h2 (q : Pattern) (selected : d73807 q = 0) : d73934 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d73807, d73934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73807, d73934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d73808 q = 0) : d73935 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d73808, d73935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73808, d73935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d73809 q = 0) : d73936 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d73809, d73936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73809, d73936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d73810 q = 0) : d73937 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d73810, d73937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73810, d73937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d73811 q = 0) : d73938 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d73811, d73938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73811, d73938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3200 (p : Pattern) (selected : d73816 p = 0) : d73943 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d73813 q = 0) : d73940 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d73813, d73940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro359 q selected
    | true =>
      simp only [d73813, d73940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d73814 q = 0) : d73941 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d73814, d73941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73814, d73941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d73815 q = 0) : d73942 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d73815, d73942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d73815, d73942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d73816 q = 0) : d73943 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d73816, d73943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d73816, d73943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro3201 (p : Pattern) (selected : d73822 p = 0) : d73949 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d73817 q = 0) : d73944 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d73817, d73944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73817, d73944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3200 q selected
  have h2 (q : Pattern) (selected : d73818 q = 0) : d73945 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d73818, d73945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73818, d73945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d73819 q = 0) : d73946 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d73819, d73946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73819, d73946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d73820 q = 0) : d73947 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d73820, d73947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73820, d73947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d73821 q = 0) : d73948 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d73821, d73948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73821, d73948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d73822 q = 0) : d73949 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d73822, d73949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73822, d73949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3202 (p : Pattern) (selected : d73828 p = 0) : d73955 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d73825 q = 0) : d73952 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d73825, d73952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro435 q selected
    | true =>
      simp only [d73825, d73952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d73826 q = 0) : d73953 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d73826, d73953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73826, d73953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d73827 q = 0) : d73954 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d73827, d73954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d73827, d73954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d73828 q = 0) : d73955 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d73828, d73955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d73828, d73955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro3203 (p : Pattern) (selected : d73834 p = 0) : d73961 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d73829 q = 0) : d73956 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d73829, d73956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73829, d73956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3202 q selected
  have h2 (q : Pattern) (selected : d73830 q = 0) : d73957 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d73830, d73957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73830, d73957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d73831 q = 0) : d73958 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d73831, d73958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73831, d73958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d73832 q = 0) : d73959 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d73832, d73959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73832, d73959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d73833 q = 0) : d73960 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d73833, d73960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73833, d73960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d73834 q = 0) : d73961 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d73834, d73961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73834, d73961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3204 (p : Pattern) (selected : d73841 p = 0) : d73968 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d73838 q = 0) : d73965 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d73838, d73965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro521 q selected
    | true =>
      simp only [d73838, d73965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d73839 q = 0) : d73966 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d73839, d73966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73839, d73966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d73840 q = 0) : d73967 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d73840, d73967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d73840, d73967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d73841 q = 0) : d73968 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d73841, d73968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d73841, d73968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro3205 (p : Pattern) (selected : d73847 p = 0) : d73974 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d73842 q = 0) : d73969 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d73842, d73969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73842, d73969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3204 q selected
  have h2 (q : Pattern) (selected : d73843 q = 0) : d73970 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d73843, d73970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73843, d73970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d73844 q = 0) : d73971 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d73844, d73971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73844, d73971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d73845 q = 0) : d73972 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d73845, d73972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73845, d73972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d73846 q = 0) : d73973 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d73846, d73973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73846, d73973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d73847 q = 0) : d73974 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d73847, d73974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73847, d73974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3206 (p : Pattern) (selected : d73855 p = 0) : d73982 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d73852 q = 0) : d73979 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d73852, d73979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro611 q selected
    | true =>
      simp only [d73852, d73979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d73853 q = 0) : d73980 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d73853, d73980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73853, d73980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d73854 q = 0) : d73981 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d73854, d73981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d73854, d73981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d73855 q = 0) : d73982 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d73855, d73982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d73855, d73982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro3207 (p : Pattern) (selected : d73861 p = 0) : d73988 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d73856 q = 0) : d73983 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d73856, d73983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73856, d73983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3206 q selected
  have h2 (q : Pattern) (selected : d73857 q = 0) : d73984 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d73857, d73984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73857, d73984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d73858 q = 0) : d73985 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d73858, d73985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73858, d73985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d73859 q = 0) : d73986 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d73859, d73986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73859, d73986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d73860 q = 0) : d73987 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d73860, d73987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73860, d73987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d73861 q = 0) : d73988 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d73861, d73988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73861, d73988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3208 (p : Pattern) (selected : d73867 p = 0) : d73994 p = 1 := by
  have h0 (q : Pattern) (selected : d73812 q = 0) : d73939 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d73812, d73939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3197 q selected
    | true =>
      simp only [d73812, d73939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3199 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d73823 q = 0) : d73950 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d73823, d73950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d73823, d73950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3201 q selected
  have h3 (q : Pattern) (selected : d73824 q = 0) : d73951 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d73824, d73951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73824, d73951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d73835 q = 0) : d73962 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d73835, d73962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d73835, d73962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3203 q selected
  have h5 (q : Pattern) (selected : d73836 q = 0) : d73963 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d73836, d73963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d73836, d73963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d73837 q = 0) : d73964 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d73837, d73964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d73837, d73964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d73848 q = 0) : d73975 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d73848, d73975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d73848, d73975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3205 q selected
  have h8 (q : Pattern) (selected : d73849 q = 0) : d73976 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d73849, d73976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d73849, d73976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d73850 q = 0) : d73977 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d73850, d73977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d73850, d73977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d73851 q = 0) : d73978 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d73851, d73978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d73851, d73978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d73862 q = 0) : d73989 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d73862, d73989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d73862, d73989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3207 q selected
  have h12 (q : Pattern) (selected : d73863 q = 0) : d73990 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d73863, d73990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d73863, d73990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d73864 q = 0) : d73991 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d73864, d73991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d73864, d73991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d73865 q = 0) : d73992 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d73865, d73992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d73865, d73992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d73866 q = 0) : d73993 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d73866, d73993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d73866, d73993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d73867 q = 0) : d73994 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d73867, d73994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d73867, d73994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro3209 (p : Pattern) (selected : d73873 p = 0) : d74000 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d73868 q = 0) : d73995 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d73868, d73995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3208 q selected
    | true =>
      simp only [d73868, d73995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d73869 q = 0) : d73996 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d73869, d73996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d73869, d73996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d73870 q = 0) : d73997 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d73870, d73997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d73870, d73997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d73871 q = 0) : d73998 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d73871, d73998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d73871, d73998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d73872 q = 0) : d73999 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d73872, d73999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d73872, d73999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d73873 q = 0) : d74000 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d73873, d74000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d73873, d74000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3210 (p : Pattern) (selected : d73879 p = 0) : d74006 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d73874 q = 0) : d74001 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d73874, d74001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3209 q selected
    | true =>
      simp only [d73874, d74001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d73875 q = 0) : d74002 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d73875, d74002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d73875, d74002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d73876 q = 0) : d74003 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d73876, d74003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d73876, d74003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d73877 q = 0) : d74004 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d73877, d74004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d73877, d74004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d73878 q = 0) : d74005 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d73878, d74005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d73878, d74005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d73879 q = 0) : d74006 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d73879, d74006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d73879, d74006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3211 (p : Pattern) (selected : d73885 p = 0) : d74012 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d73880 q = 0) : d74007 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d73880, d74007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3210 q selected
    | true =>
      simp only [d73880, d74007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d73881 q = 0) : d74008 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d73881, d74008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d73881, d74008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d73882 q = 0) : d74009 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d73882, d74009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d73882, d74009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d73883 q = 0) : d74010 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d73883, d74010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d73883, d74010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d73884 q = 0) : d74011 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d73884, d74011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d73884, d74011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d73885 q = 0) : d74012 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d73885, d74012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d73885, d74012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3212 (p : Pattern) (selected : d73891 p = 0) : d74018 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d73886 q = 0) : d74013 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d73886, d74013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3211 q selected
    | true =>
      simp only [d73886, d74013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d73887 q = 0) : d74014 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d73887, d74014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d73887, d74014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d73888 q = 0) : d74015 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d73888, d74015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d73888, d74015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d73889 q = 0) : d74016 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d73889, d74016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d73889, d74016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d73890 q = 0) : d74017 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d73890, d74017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d73890, d74017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d73891 q = 0) : d74018 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d73891, d74018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d73891, d74018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3213 (p : Pattern) (selected : d73897 p = 0) : d74024 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d73892 q = 0) : d74019 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d73892, d74019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3212 q selected
    | true =>
      simp only [d73892, d74019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d73893 q = 0) : d74020 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d73893, d74020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d73893, d74020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d73894 q = 0) : d74021 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d73894, d74021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d73894, d74021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d73895 q = 0) : d74022 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d73895, d74022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d73895, d74022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d73896 q = 0) : d74023 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d73896, d74023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d73896, d74023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d73897 q = 0) : d74024 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d73897, d74024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d73897, d74024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3214 (p : Pattern) (selected : d73903 p = 0) : d74030 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d73898 q = 0) : d74025 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d73898, d74025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3213 q selected
    | true =>
      simp only [d73898, d74025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d73899 q = 0) : d74026 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d73899, d74026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d73899, d74026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d73900 q = 0) : d74027 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d73900, d74027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d73900, d74027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d73901 q = 0) : d74028 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d73901, d74028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d73901, d74028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d73902 q = 0) : d74029 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d73902, d74029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d73902, d74029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d73903 q = 0) : d74030 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d73903, d74030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d73903, d74030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3215 (p : Pattern) (selected : d73909 p = 0) : d74036 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d73904 q = 0) : d74031 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d73904, d74031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3214 q selected
    | true =>
      simp only [d73904, d74031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d73905 q = 0) : d74032 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d73905, d74032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d73905, d74032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d73906 q = 0) : d74033 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d73906, d74033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d73906, d74033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d73907 q = 0) : d74034 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d73907, d74034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d73907, d74034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d73908 q = 0) : d74035 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d73908, d74035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d73908, d74035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d73909 q = 0) : d74036 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d73909, d74036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d73909, d74036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3216 (p : Pattern) (selected : d73909 p = 1) : d73909 p = 1 := by
  have h0 (q : Pattern) (selected : d73909 q = 1) : d73909 q = 1 := by
    exact selected
  exact h0 p selected
theorem eqIntro3217 (p : Pattern) (selected : d3675 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d117 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro660 q selected
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d119 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d120 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3674 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3675 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3218 (p : Pattern) (selected : d3677 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d117 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro660 q selected
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d119 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d120 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3674 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro673 q selected
    | true =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d196 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d197 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d198 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d3676 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d3677 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro3219 (p : Pattern) (selected : d3683 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3678 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3217 q selected
    | true =>
      simp only [d3678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3218 q selected
  have h2 (q : Pattern) (selected : d3679 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3680 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3681 q = 2) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3682 q = 2) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3683 q = 2) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3220 (p : Pattern) (selected : d3690 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d297 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro690 q selected
    | true =>
      simp only [d297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro660 q selected
  have h2 (q : Pattern) (selected : d298 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d299 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d300 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3689 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3690 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3221 (p : Pattern) (selected : d3692 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d297 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro690 q selected
    | true =>
      simp only [d297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro660 q selected
  have h2 (q : Pattern) (selected : d298 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d299 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d300 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3689 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d377 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro703 q selected
    | true =>
      simp only [d377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro673 q selected
  have h7 (q : Pattern) (selected : d378 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d379 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d380 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d3691 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d3692 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro3222 (p : Pattern) (selected : d3698 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3693 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3220 q selected
    | true =>
      simp only [d3693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3221 q selected
  have h2 (q : Pattern) (selected : d3694 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3695 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3696 q = 2) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3697 q = 2) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3698 q = 2) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3223 (p : Pattern) (selected : d3704 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3684 q = 2) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3219 q selected
  have h2 (q : Pattern) (selected : d3685 q = 2) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3686 q = 2) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3687 q = 2) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3688 q = 2) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3699 q = 2) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3222 q selected
  have h7 (q : Pattern) (selected : d3700 q = 2) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d3701 q = 2) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3702 q = 2) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d3703 q = 2) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d3704 q = 2) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro3224 (p : Pattern) (selected : d3706 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d515 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro729 q selected
    | true =>
      simp only [d515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro730 q selected
  have h2 (q : Pattern) (selected : d516 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d517 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d518 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3705 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3706 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3225 (p : Pattern) (selected : d3708 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d515 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro729 q selected
    | true =>
      simp only [d515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro730 q selected
  have h2 (q : Pattern) (selected : d516 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d517 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d518 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3705 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d611 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro747 q selected
    | true =>
      simp only [d611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro748 q selected
  have h7 (q : Pattern) (selected : d612 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d613 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d614 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d3707 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d3708 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro3226 (p : Pattern) (selected : d3714 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3709 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3224 q selected
    | true =>
      simp only [d3709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3225 q selected
  have h2 (q : Pattern) (selected : d3710 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3711 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3712 q = 2) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3713 q = 2) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3714 q = 2) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3227 (p : Pattern) (selected : d3720 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3715 q = 2) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3226 q selected
  have h2 (q : Pattern) (selected : d3716 q = 2) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3717 q = 2) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3718 q = 2) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3719 q = 2) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3720 q = 2) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3228 (p : Pattern) (selected : d3723 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d807 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro787 q selected
    | true =>
      simp only [d807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro788 q selected
  have h2 (q : Pattern) (selected : d808 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d809 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d810 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3722 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3723 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3229 (p : Pattern) (selected : d3725 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d807 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro787 q selected
    | true =>
      simp only [d807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro788 q selected
  have h2 (q : Pattern) (selected : d808 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d809 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d810 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3722 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d917 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro809 q selected
    | true =>
      simp only [d917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro810 q selected
  have h7 (q : Pattern) (selected : d918 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d919 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d920 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d3724 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d3725 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro3230 (p : Pattern) (selected : d3731 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3726 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3228 q selected
    | true =>
      simp only [d3726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3229 q selected
  have h2 (q : Pattern) (selected : d3727 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3728 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3729 q = 2) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3730 q = 2) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3731 q = 2) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3231 (p : Pattern) (selected : d3737 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3732 q = 2) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3230 q selected
  have h2 (q : Pattern) (selected : d3733 q = 2) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3734 q = 2) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3735 q = 2) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3736 q = 2) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3737 q = 2) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3232 (p : Pattern) (selected : d3741 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1186 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro859 q selected
    | true =>
      simp only [d1186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro860 q selected
  have h2 (q : Pattern) (selected : d1187 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1188 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1189 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3740 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3741 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3233 (p : Pattern) (selected : d3743 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1186 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro859 q selected
    | true =>
      simp only [d1186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro860 q selected
  have h2 (q : Pattern) (selected : d1187 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1188 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1189 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3740 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d1328 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro885 q selected
    | true =>
      simp only [d1328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro886 q selected
  have h7 (q : Pattern) (selected : d1329 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1330 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1331 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d3742 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d3743 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro3234 (p : Pattern) (selected : d3749 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3744 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3232 q selected
    | true =>
      simp only [d3744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3233 q selected
  have h2 (q : Pattern) (selected : d3745 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3746 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3747 q = 2) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3748 q = 2) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3749 q = 2) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3235 (p : Pattern) (selected : d3755 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3750 q = 2) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3234 q selected
  have h2 (q : Pattern) (selected : d3751 q = 2) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3752 q = 2) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3753 q = 2) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3754 q = 2) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3755 q = 2) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3236 (p : Pattern) (selected : d3760 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1647 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro941 q selected
    | true =>
      simp only [d1647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro942 q selected
  have h2 (q : Pattern) (selected : d1648 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1649 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1650 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3759 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3760 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3237 (p : Pattern) (selected : d3762 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1647 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro941 q selected
    | true =>
      simp only [d1647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro942 q selected
  have h2 (q : Pattern) (selected : d1648 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1649 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1650 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3759 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d1805 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro971 q selected
    | true =>
      simp only [d1805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro972 q selected
  have h7 (q : Pattern) (selected : d1806 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1807 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1808 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d3761 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d3762 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro3238 (p : Pattern) (selected : d3768 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3763 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3236 q selected
    | true =>
      simp only [d3763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3237 q selected
  have h2 (q : Pattern) (selected : d3764 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3765 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3766 q = 2) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3767 q = 2) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3768 q = 2) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3239 (p : Pattern) (selected : d3774 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3769 q = 2) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3238 q selected
  have h2 (q : Pattern) (selected : d3770 q = 2) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3771 q = 2) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3772 q = 2) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3773 q = 2) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3774 q = 2) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3240 (p : Pattern) (selected : d3780 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2130 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1030 q selected
    | true =>
      simp only [d2130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1031 q selected
  have h2 (q : Pattern) (selected : d2131 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2132 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2133 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3779 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3780 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3241 (p : Pattern) (selected : d3782 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2130 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1030 q selected
    | true =>
      simp only [d2130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1031 q selected
  have h2 (q : Pattern) (selected : d2131 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2132 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2133 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3779 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2283 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1061 q selected
    | true =>
      simp only [d2283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1062 q selected
  have h7 (q : Pattern) (selected : d2284 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d2285 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d2286 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d3781 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d3782 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro3242 (p : Pattern) (selected : d3788 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3783 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3240 q selected
    | true =>
      simp only [d3783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3241 q selected
  have h2 (q : Pattern) (selected : d3784 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3785 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3786 q = 2) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3787 q = 2) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3788 q = 2) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3243 (p : Pattern) (selected : d3794 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3789 q = 2) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3242 q selected
  have h2 (q : Pattern) (selected : d3790 q = 2) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3791 q = 2) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3792 q = 2) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3793 q = 2) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3794 q = 2) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro3244 (p : Pattern) (selected : d3800 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d3721 q = 2) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3223 q selected
    | true =>
      simp only [d3721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3227 q selected
  have h1 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h2 (q : Pattern) (selected : d3738 q = 2) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3231 q selected
  have h3 (q : Pattern) (selected : d3739 q = 2) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3756 q = 2) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3235 q selected
  have h5 (q : Pattern) (selected : d3757 q = 2) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3758 q = 2) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3775 q = 2) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3239 q selected
  have h8 (q : Pattern) (selected : d3776 q = 2) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3777 q = 2) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d3778 q = 2) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d3778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d3795 q = 2) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3243 q selected
  have h12 (q : Pattern) (selected : d3796 q = 2) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d3797 q = 2) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d3798 q = 2) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d3798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d3799 q = 2) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d3799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d3799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d3800 q = 2) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d3800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d3800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro3245 (p : Pattern) (selected : d3806 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3801 q = 2) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d3801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3244 q selected
    | true =>
      simp only [d3801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3802 q = 2) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d3802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3803 q = 2) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d3803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3804 q = 2) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d3804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3805 q = 2) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d3805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3806 q = 2) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d3806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3246 (p : Pattern) (selected : d3812 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3807 q = 2) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d3807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3245 q selected
    | true =>
      simp only [d3807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3808 q = 2) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d3808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3809 q = 2) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d3809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3810 q = 2) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d3810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3811 q = 2) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d3811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3812 q = 2) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d3812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3247 (p : Pattern) (selected : d3818 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3813 q = 2) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d3813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3246 q selected
    | true =>
      simp only [d3813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3814 q = 2) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d3814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3815 q = 2) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d3815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3816 q = 2) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d3816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3817 q = 2) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d3817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3818 q = 2) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d3818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3248 (p : Pattern) (selected : d3824 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3819 q = 2) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d3819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3247 q selected
    | true =>
      simp only [d3819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3820 q = 2) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d3820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3821 q = 2) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d3821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3822 q = 2) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d3822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3823 q = 2) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d3823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3824 q = 2) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d3824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro3249 (p : Pattern) (selected : d3830 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d3825 q = 2) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d3825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3248 q selected
    | true =>
      simp only [d3825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3826 q = 2) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d3826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3827 q = 2) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d3827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3828 q = 2) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d3828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3829 q = 2) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d3829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3830 q = 2) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d3830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
end NetHack.Soko22Hazard87
