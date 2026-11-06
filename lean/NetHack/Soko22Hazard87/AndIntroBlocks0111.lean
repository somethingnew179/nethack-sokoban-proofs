import NetHack.Soko22Hazard87.AndIntroBlocks0110
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro27750 (p : Pattern) (ha : d94263 p = 1) (hb : d126678 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d94220 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d94220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d94220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11648 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d94221 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d94221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d94221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d94222 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d94222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d94222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d94223 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d94223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d94223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d94224 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d94224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d94224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94258 q = 1) (hb : d126673 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94258, d126673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94258, d126673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27749 q ha hb
  have h8 (q : Pattern) (ha : d94259 q = 1) (hb : d126674 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94259, d126674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94259, d126674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94260 q = 1) (hb : d126675 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94260, d126675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94260, d126675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94261 q = 1) (hb : d126676 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94261, d126676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94261, d126676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94262 q = 1) (hb : d126677 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94262, d126677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94262, d126677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d94263 q = 1) (hb : d126678 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94263, d126678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d94263, d126678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro27751 (p : Pattern) (ha : d94268 p = 1) (hb : d125930 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8444 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8450 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d8464 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d125925 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94264 q = 1) (hb : d125926 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94264, d125926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d94264, d125926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d8481 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d94265 q = 1) (hb : d125927 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94265, d125927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94265, d125927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d94266 q = 1) (hb : d125928 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94266, d125928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94266, d125928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94267 q = 1) (hb : d125929 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94267, d125929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94267, d125929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94268 q = 1) (hb : d125930 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94268, d125930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94268, d125930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro27752 (p : Pattern) (ha : d94273 p = 1) (hb : d125939 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8444 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8450 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8464 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d125925 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d94264 q = 1) (hb : d125926 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94264, d125926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94264, d125926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d8481 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d94265 q = 1) (hb : d125927 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94265, d125927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94265, d125927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d94266 q = 1) (hb : d125928 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94266, d125928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94266, d125928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94267 q = 1) (hb : d125929 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94267, d125929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94267, d125929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d8490 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d8494 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d8497 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d125934 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d94269 q = 1) (hb : d125935 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94269, d125935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d94269, d125935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d8503 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94270 q = 1) (hb : d125936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94270, d125936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94270, d125936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d94271 q = 1) (hb : d125937 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94271, d125937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94271, d125937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94272 q = 1) (hb : d125938 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94272, d125938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94272, d125938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d94273 q = 1) (hb : d125939 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94273, d125939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94273, d125939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro27753 (p : Pattern) (ha : d94280 p = 1) (hb : d126681 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8497 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d125934 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94269 q = 1) (hb : d125935 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94269, d125935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94269, d125935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8503 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94270 q = 1) (hb : d125936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94270, d125936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94270, d125936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94278 q = 1) (hb : d125937 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94278, d125937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94278, d125937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94279 q = 1) (hb : d125938 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94279, d125938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94279, d125938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94280 q = 1) (hb : d126681 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94280, d126681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94280, d126681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27754 (p : Pattern) (ha : d94290 p = 1) (hb : d126692 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8540 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126687 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94286 q = 1) (hb : d126688 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94286, d126688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94286, d126688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8557 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94287 q = 1) (hb : d126689 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94287, d126689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94287, d126689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94288 q = 1) (hb : d126690 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94288, d126690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94288, d126690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94289 q = 1) (hb : d126691 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94289, d126691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94289, d126691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94290 q = 1) (hb : d126692 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94290, d126692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94290, d126692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27755 (p : Pattern) (ha : d94296 p = 1) (hb : d126698 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8438 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94274 q = 1) (hb : d125940 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94274, d125940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27751 q ha hb
    | true =>
      simp only [d94274, d125940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27752 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8515 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94275 q = 1) (hb : d125941 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94275, d125941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94275, d125941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94276 q = 1) (hb : d126679 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94276, d126679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94276, d126679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94277 q = 1) (hb : d126680 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94277, d126680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94277, d126680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94281 q = 1) (hb : d126682 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94281, d126682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94281, d126682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27753 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d654 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d94282 q = 1) (hb : d126683 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94282, d126683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94282, d126683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d94283 q = 1) (hb : d126684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94283, d126684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94283, d126684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d94284 q = 1) (hb : d126685 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94284, d126685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94284, d126685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d94285 q = 1) (hb : d126686 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94285, d126686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94285, d126686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94291 q = 1) (hb : d126693 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94291, d126693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94291, d126693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27754 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d737 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94292 q = 1) (hb : d126694 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94292, d126694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94292, d126694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d94293 q = 1) (hb : d126695 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94293, d126695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94293, d126695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d94294 q = 1) (hb : d126696 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94294, d126696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94294, d126696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d94295 q = 1) (hb : d126697 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94295, d126697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94295, d126697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d94296 q = 1) (hb : d126698 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94296, d126698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94296, d126698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro27756 (p : Pattern) (ha : d94302 p = 1) (hb : d126704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94297 q = 1) (hb : d126699 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94297, d126699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94297, d126699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27755 q ha hb
  have h2 (q : Pattern) (ha : d94298 q = 1) (hb : d126700 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94298, d126700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94298, d126700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94299 q = 1) (hb : d126701 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94299, d126701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94299, d126701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94300 q = 1) (hb : d126702 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94300, d126702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94300, d126702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94301 q = 1) (hb : d126703 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94301, d126703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94301, d126703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94302 q = 1) (hb : d126704 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94302, d126704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94302, d126704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27757 (p : Pattern) (ha : d94308 p = 1) (hb : d126063 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8606 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8612 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d8626 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d126058 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94304 q = 1) (hb : d126059 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94304, d126059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d94304, d126059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d8643 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d94305 q = 1) (hb : d126060 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94305, d126060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94305, d126060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d94306 q = 1) (hb : d126061 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94306, d126061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94306, d126061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94307 q = 1) (hb : d126062 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94307, d126062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94307, d126062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94308 q = 1) (hb : d126063 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94308, d126063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94308, d126063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro27758 (p : Pattern) (ha : d94313 p = 1) (hb : d126072 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8606 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8612 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8626 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d126058 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d94304 q = 1) (hb : d126059 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94304, d126059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94304, d126059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d8643 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d94305 q = 1) (hb : d126060 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94305, d126060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94305, d126060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d94306 q = 1) (hb : d126061 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94306, d126061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94306, d126061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94307 q = 1) (hb : d126062 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94307, d126062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94307, d126062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d8652 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d8656 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d8659 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d126067 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d94309 q = 1) (hb : d126068 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94309, d126068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d94309, d126068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d8665 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94310 q = 1) (hb : d126069 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94310, d126069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94310, d126069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d94311 q = 1) (hb : d126070 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94311, d126070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94311, d126070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94312 q = 1) (hb : d126071 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94312, d126071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94312, d126071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d94313 q = 1) (hb : d126072 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94313, d126072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94313, d126072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro27759 (p : Pattern) (ha : d94320 p = 1) (hb : d126708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8659 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126067 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94309 q = 1) (hb : d126068 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94309, d126068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94309, d126068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8665 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94310 q = 1) (hb : d126069 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94310, d126069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94310, d126069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94318 q = 1) (hb : d126070 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94318, d126070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94318, d126070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94319 q = 1) (hb : d126071 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94319, d126071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94319, d126071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94320 q = 1) (hb : d126708 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94320, d126708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94320, d126708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27760 (p : Pattern) (ha : d94330 p = 1) (hb : d126719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8702 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126714 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94326 q = 1) (hb : d126715 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94326, d126715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94326, d126715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8723 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94327 q = 1) (hb : d126716 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94327, d126716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94327, d126716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94328 q = 1) (hb : d126717 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94328, d126717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94328, d126717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94329 q = 1) (hb : d126718 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94329, d126718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94329, d126718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94330 q = 1) (hb : d126719 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94330, d126719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94330, d126719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27761 (p : Pattern) (ha : d94336 p = 1) (hb : d126725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8600 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94314 q = 1) (hb : d126073 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94314, d126073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27757 q ha hb
    | true =>
      simp only [d94314, d126073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27758 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8677 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94315 q = 1) (hb : d126074 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94315, d126074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94315, d126074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94316 q = 1) (hb : d126706 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94316, d126706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94316, d126706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94317 q = 1) (hb : d126707 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94317, d126707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94317, d126707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94321 q = 1) (hb : d126709 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94321, d126709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94321, d126709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27759 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d960 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d94322 q = 1) (hb : d126710 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94322, d126710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94322, d126710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d94323 q = 1) (hb : d126711 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94323, d126711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94323, d126711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d94324 q = 1) (hb : d126712 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94324, d126712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94324, d126712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d94325 q = 1) (hb : d126713 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94325, d126713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94325, d126713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94331 q = 1) (hb : d126720 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94331, d126720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94331, d126720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27760 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1070 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94332 q = 1) (hb : d126721 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94332, d126721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94332, d126721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d94333 q = 1) (hb : d126722 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94333, d126722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94333, d126722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d94334 q = 1) (hb : d126723 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94334, d126723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94334, d126723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d94335 q = 1) (hb : d126724 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94335, d126724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94335, d126724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d94336 q = 1) (hb : d126725 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94336, d126725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94336, d126725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro27762 (p : Pattern) (ha : d94342 p = 1) (hb : d126731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94337 q = 1) (hb : d126726 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94337, d126726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94337, d126726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27761 q ha hb
  have h2 (q : Pattern) (ha : d94338 q = 1) (hb : d126727 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94338, d126727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94338, d126727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94339 q = 1) (hb : d126728 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94339, d126728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94339, d126728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94340 q = 1) (hb : d126729 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94340, d126729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94340, d126729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94341 q = 1) (hb : d126730 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94341, d126730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94341, d126730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94342 q = 1) (hb : d126731 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94342, d126731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94342, d126731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27763 (p : Pattern) (ha : d94349 p = 1) (hb : d126202 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8773 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8779 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d8793 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d126197 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94345 q = 1) (hb : d126198 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94345, d126198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d94345, d126198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d8810 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d94346 q = 1) (hb : d126199 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94346, d126199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94346, d126199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d94347 q = 1) (hb : d126200 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94347, d126200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94347, d126200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94348 q = 1) (hb : d126201 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94348, d126201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94348, d126201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94349 q = 1) (hb : d126202 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94349, d126202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94349, d126202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro27764 (p : Pattern) (ha : d94354 p = 1) (hb : d126211 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8779 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8793 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d126197 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d94345 q = 1) (hb : d126198 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94345, d126198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94345, d126198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d8810 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d94346 q = 1) (hb : d126199 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94346, d126199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94346, d126199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d94347 q = 1) (hb : d126200 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94347, d126200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94347, d126200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94348 q = 1) (hb : d126201 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94348, d126201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94348, d126201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d8819 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d8823 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d8826 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d126206 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d94350 q = 1) (hb : d126207 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94350, d126207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d94350, d126207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d8832 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94351 q = 1) (hb : d126208 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94351, d126208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94351, d126208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d94352 q = 1) (hb : d126209 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94352, d126209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94352, d126209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94353 q = 1) (hb : d126210 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94353, d126210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94353, d126210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d94354 q = 1) (hb : d126211 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94354, d126211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94354, d126211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro27765 (p : Pattern) (ha : d94361 p = 1) (hb : d126736 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8826 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126206 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94350 q = 1) (hb : d126207 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94350, d126207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94350, d126207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8832 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94351 q = 1) (hb : d126208 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94351, d126208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94351, d126208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94359 q = 1) (hb : d126209 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94359, d126209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94359, d126209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94360 q = 1) (hb : d126210 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94360, d126210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94360, d126210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94361 q = 1) (hb : d126736 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94361, d126736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94361, d126736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27766 (p : Pattern) (ha : d94371 p = 1) (hb : d126747 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8869 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126742 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94367 q = 1) (hb : d126743 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94367, d126743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94367, d126743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8890 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94368 q = 1) (hb : d126744 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94368, d126744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94368, d126744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94369 q = 1) (hb : d126745 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94369, d126745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94369, d126745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94370 q = 1) (hb : d126746 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94370, d126746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94370, d126746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94371 q = 1) (hb : d126747 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94371, d126747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94371, d126747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27767 (p : Pattern) (ha : d94377 p = 1) (hb : d126753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8767 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94355 q = 1) (hb : d126212 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94355, d126212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27763 q ha hb
    | true =>
      simp only [d94355, d126212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27764 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8844 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94356 q = 1) (hb : d126213 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94356, d126213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94356, d126213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94357 q = 1) (hb : d126734 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94357, d126734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94357, d126734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94358 q = 1) (hb : d126735 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94358, d126735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94358, d126735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94362 q = 1) (hb : d126737 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94362, d126737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94362, d126737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27765 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1371 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d94363 q = 1) (hb : d126738 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94363, d126738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94363, d126738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d94364 q = 1) (hb : d126739 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94364, d126739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94364, d126739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d94365 q = 1) (hb : d126740 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94365, d126740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94365, d126740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d94366 q = 1) (hb : d126741 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94366, d126741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94366, d126741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94372 q = 1) (hb : d126748 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94372, d126748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94372, d126748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27766 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1504 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94373 q = 1) (hb : d126749 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94373, d126749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94373, d126749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d94374 q = 1) (hb : d126750 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94374, d126750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94374, d126750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d94375 q = 1) (hb : d126751 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94375, d126751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94375, d126751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d94376 q = 1) (hb : d126752 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94376, d126752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94376, d126752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d94377 q = 1) (hb : d126753 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94377, d126753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94377, d126753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro27768 (p : Pattern) (ha : d94383 p = 1) (hb : d126759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94378 q = 1) (hb : d126754 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94378, d126754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94378, d126754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27767 q ha hb
  have h2 (q : Pattern) (ha : d94379 q = 1) (hb : d126755 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94379, d126755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94379, d126755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94380 q = 1) (hb : d126756 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94380, d126756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94380, d126756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94381 q = 1) (hb : d126757 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94381, d126757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94381, d126757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94382 q = 1) (hb : d126758 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94382, d126758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94382, d126758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94383 q = 1) (hb : d126759 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94383, d126759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94383, d126759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27769 (p : Pattern) (ha : d94391 p = 1) (hb : d126342 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8941 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8947 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d8961 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d126337 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94387 q = 1) (hb : d126338 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94387, d126338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d94387, d126338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d8978 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d94388 q = 1) (hb : d126339 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94388, d126339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94388, d126339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d94389 q = 1) (hb : d126340 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94389, d126340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94389, d126340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94390 q = 1) (hb : d126341 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94390, d126341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94390, d126341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94391 q = 1) (hb : d126342 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94391, d126342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94391, d126342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro27770 (p : Pattern) (ha : d94396 p = 1) (hb : d126351 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8947 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8961 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d126337 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d94387 q = 1) (hb : d126338 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94387, d126338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94387, d126338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d8978 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d94388 q = 1) (hb : d126339 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94388, d126339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94388, d126339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d94389 q = 1) (hb : d126340 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94389, d126340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94389, d126340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94390 q = 1) (hb : d126341 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94390, d126341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94390, d126341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d8987 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d8991 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d8994 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d126346 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d94392 q = 1) (hb : d126347 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94392, d126347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d94392, d126347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d9000 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94393 q = 1) (hb : d126348 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94393, d126348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94393, d126348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d94394 q = 1) (hb : d126349 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94394, d126349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94394, d126349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94395 q = 1) (hb : d126350 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94395, d126350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94395, d126350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d94396 q = 1) (hb : d126351 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94396, d126351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94396, d126351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro27771 (p : Pattern) (ha : d94403 p = 1) (hb : d126765 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8994 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126346 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94392 q = 1) (hb : d126347 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94392, d126347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94392, d126347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d9000 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94393 q = 1) (hb : d126348 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94393, d126348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94393, d126348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94401 q = 1) (hb : d126349 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94401, d126349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94401, d126349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94402 q = 1) (hb : d126350 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94402, d126350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94402, d126350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94403 q = 1) (hb : d126765 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94403, d126765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94403, d126765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27772 (p : Pattern) (ha : d94413 p = 1) (hb : d126776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9037 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126771 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94409 q = 1) (hb : d126772 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94409, d126772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94409, d126772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d9058 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94410 q = 1) (hb : d126773 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94410, d126773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94410, d126773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94411 q = 1) (hb : d126774 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94411, d126774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94411, d126774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94412 q = 1) (hb : d126775 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94412, d126775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94412, d126775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94413 q = 1) (hb : d126776 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94413, d126776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94413, d126776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27773 (p : Pattern) (ha : d94419 p = 1) (hb : d126782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8935 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94397 q = 1) (hb : d126352 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94397, d126352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27769 q ha hb
    | true =>
      simp only [d94397, d126352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27770 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9012 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94398 q = 1) (hb : d126353 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94398, d126353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94398, d126353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94399 q = 1) (hb : d126763 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94399, d126763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94399, d126763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94400 q = 1) (hb : d126764 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94400, d126764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94400, d126764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94404 q = 1) (hb : d126766 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94404, d126766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94404, d126766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27771 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1848 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d94405 q = 1) (hb : d126767 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94405, d126767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94405, d126767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d94406 q = 1) (hb : d126768 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94406, d126768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94406, d126768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d94407 q = 1) (hb : d126769 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94407, d126769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94407, d126769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d94408 q = 1) (hb : d126770 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94408, d126770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94408, d126770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94414 q = 1) (hb : d126777 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94414, d126777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94414, d126777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27772 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1981 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94415 q = 1) (hb : d126778 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94415, d126778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94415, d126778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d94416 q = 1) (hb : d126779 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94416, d126779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94416, d126779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d94417 q = 1) (hb : d126780 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94417, d126780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94417, d126780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d94418 q = 1) (hb : d126781 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94418, d126781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94418, d126781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d94419 q = 1) (hb : d126782 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94419, d126782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94419, d126782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro27774 (p : Pattern) (ha : d94425 p = 1) (hb : d126788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94420 q = 1) (hb : d126783 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94420, d126783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94420, d126783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27773 q ha hb
  have h2 (q : Pattern) (ha : d94421 q = 1) (hb : d126784 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94421, d126784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94421, d126784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94422 q = 1) (hb : d126785 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94422, d126785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94422, d126785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94423 q = 1) (hb : d126786 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94423, d126786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94423, d126786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94424 q = 1) (hb : d126787 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94424, d126787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94424, d126787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94425 q = 1) (hb : d126788 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94425, d126788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94425, d126788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27775 (p : Pattern) (ha : d94434 p = 1) (hb : d126483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9110 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9116 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d9130 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d126478 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94430 q = 1) (hb : d126479 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94430, d126479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d94430, d126479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d9147 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d94431 q = 1) (hb : d126480 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94431, d126480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94431, d126480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d94432 q = 1) (hb : d126481 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94432, d126481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94432, d126481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94433 q = 1) (hb : d126482 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94433, d126482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94433, d126482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94434 q = 1) (hb : d126483 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94434, d126483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94434, d126483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro27776 (p : Pattern) (ha : d94439 p = 1) (hb : d126492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d9110 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9116 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9130 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d126478 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d94430 q = 1) (hb : d126479 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94430, d126479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94430, d126479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d9147 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d94431 q = 1) (hb : d126480 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94431, d126480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94431, d126480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d94432 q = 1) (hb : d126481 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94432, d126481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94432, d126481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94433 q = 1) (hb : d126482 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94433, d126482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94433, d126482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d9156 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d9160 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d9163 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d126487 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d94435 q = 1) (hb : d126488 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94435, d126488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d94435, d126488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d9169 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94436 q = 1) (hb : d126489 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94436, d126489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94436, d126489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d94437 q = 1) (hb : d126490 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94437, d126490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d94437, d126490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94438 q = 1) (hb : d126491 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94438, d126491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d94438, d126491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d94439 q = 1) (hb : d126492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94439, d126492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94439, d126492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro27777 (p : Pattern) (ha : d94446 p = 1) (hb : d126795 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9163 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126487 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94435 q = 1) (hb : d126488 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94435, d126488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94435, d126488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d9169 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94436 q = 1) (hb : d126489 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94436, d126489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94436, d126489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94444 q = 1) (hb : d126490 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94444, d126490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94444, d126490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94445 q = 1) (hb : d126491 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94445, d126491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94445, d126491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94446 q = 1) (hb : d126795 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94446, d126795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94446, d126795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27778 (p : Pattern) (ha : d94456 p = 1) (hb : d126806 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9206 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126801 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94452 q = 1) (hb : d126802 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94452, d126802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94452, d126802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d9227 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94453 q = 1) (hb : d126803 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94453, d126803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94453, d126803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d94454 q = 1) (hb : d126804 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94454, d126804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94454, d126804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94455 q = 1) (hb : d126805 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94455, d126805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94455, d126805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94456 q = 1) (hb : d126806 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94456, d126806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94456, d126806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27779 (p : Pattern) (ha : d94462 p = 1) (hb : d126812 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d9104 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94440 q = 1) (hb : d126493 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94440, d126493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27775 q ha hb
    | true =>
      simp only [d94440, d126493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27776 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9181 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d94441 q = 1) (hb : d126494 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94441, d126494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94441, d126494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d94442 q = 1) (hb : d126793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94442, d126793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94442, d126793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94443 q = 1) (hb : d126794 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94443, d126794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94443, d126794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94447 q = 1) (hb : d126796 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94447, d126796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94447, d126796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27777 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d2326 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d94448 q = 1) (hb : d126797 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94448, d126797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94448, d126797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d94449 q = 1) (hb : d126798 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94449, d126798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94449, d126798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d94450 q = 1) (hb : d126799 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94450, d126799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94450, d126799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d94451 q = 1) (hb : d126800 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94451, d126800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94451, d126800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94457 q = 1) (hb : d126807 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94457, d126807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94457, d126807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27778 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d2459 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d94458 q = 1) (hb : d126808 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94458, d126808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94458, d126808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d94459 q = 1) (hb : d126809 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94459, d126809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94459, d126809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d94460 q = 1) (hb : d126810 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94460, d126810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94460, d126810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d94461 q = 1) (hb : d126811 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94461, d126811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94461, d126811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d94462 q = 1) (hb : d126812 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94462, d126812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94462, d126812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro27780 (p : Pattern) (ha : d94468 p = 1) (hb : d126818 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94463 q = 1) (hb : d126813 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94463, d126813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94463, d126813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27779 q ha hb
  have h2 (q : Pattern) (ha : d94464 q = 1) (hb : d126814 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94464, d126814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94464, d126814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d94465 q = 1) (hb : d126815 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94465, d126815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94465, d126815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94466 q = 1) (hb : d126816 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94466, d126816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94466, d126816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94467 q = 1) (hb : d126817 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94467, d126817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94467, d126817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94468 q = 1) (hb : d126818 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94468, d126818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94468, d126818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27781 (p : Pattern) (ha : d94474 p = 1) (hb : d126824 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d94303 q = 1) (hb : d126705 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94303, d126705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27750 q ha hb
    | true =>
      simp only [d94303, d126705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27756 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d94343 q = 1) (hb : d126732 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94343, d126732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94343, d126732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27762 q ha hb
  have h3 (q : Pattern) (ha : d94344 q = 1) (hb : d126733 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94344, d126733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94344, d126733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d94384 q = 1) (hb : d126760 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94384, d126760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94384, d126760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27768 q ha hb
  have h5 (q : Pattern) (ha : d94385 q = 1) (hb : d126761 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94385, d126761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94385, d126761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94386 q = 1) (hb : d126762 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94386, d126762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94386, d126762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94426 q = 1) (hb : d126789 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94426, d126789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94426, d126789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27774 q ha hb
  have h8 (q : Pattern) (ha : d94427 q = 1) (hb : d126790 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94427, d126790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94427, d126790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94428 q = 1) (hb : d126791 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94428, d126791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94428, d126791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94429 q = 1) (hb : d126792 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d94429, d126792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94429, d126792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94469 q = 1) (hb : d126819 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94469, d126819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94469, d126819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27780 q ha hb
  have h12 (q : Pattern) (ha : d94470 q = 1) (hb : d126820 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94470, d126820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94470, d126820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94471 q = 1) (hb : d126821 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94471, d126821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94471, d126821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94472 q = 1) (hb : d126822 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d94472, d126822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94472, d126822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94473 q = 1) (hb : d126823 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d94473, d126823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94473, d126823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d94474 q = 1) (hb : d126824 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d94474, d126824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94474, d126824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro27782 (p : Pattern) (ha : d94480 p = 1) (hb : d126830 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94475 q = 1) (hb : d126825 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d94475, d126825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27781 q ha hb
    | true =>
      simp only [d94475, d126825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94476 q = 1) (hb : d126826 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d94476, d126826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94476, d126826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94477 q = 1) (hb : d126827 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d94477, d126827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94477, d126827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94478 q = 1) (hb : d126828 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d94478, d126828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94478, d126828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94479 q = 1) (hb : d126829 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d94479, d126829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94479, d126829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94480 q = 1) (hb : d126830 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d94480, d126830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94480, d126830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27783 (p : Pattern) (ha : d94486 p = 1) (hb : d126836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94481 q = 1) (hb : d126831 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d94481, d126831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27782 q ha hb
    | true =>
      simp only [d94481, d126831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94482 q = 1) (hb : d126832 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d94482, d126832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94482, d126832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94483 q = 1) (hb : d126833 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d94483, d126833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94483, d126833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94484 q = 1) (hb : d126834 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d94484, d126834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94484, d126834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94485 q = 1) (hb : d126835 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d94485, d126835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94485, d126835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94486 q = 1) (hb : d126836 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d94486, d126836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94486, d126836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27784 (p : Pattern) (ha : d94492 p = 1) (hb : d126842 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94487 q = 1) (hb : d126837 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d94487, d126837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27783 q ha hb
    | true =>
      simp only [d94487, d126837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94488 q = 1) (hb : d126838 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d94488, d126838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94488, d126838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94489 q = 1) (hb : d126839 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d94489, d126839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94489, d126839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94490 q = 1) (hb : d126840 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d94490, d126840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94490, d126840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94491 q = 1) (hb : d126841 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d94491, d126841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94491, d126841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94492 q = 1) (hb : d126842 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d94492, d126842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94492, d126842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27785 (p : Pattern) (ha : d94498 p = 1) (hb : d126848 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94493 q = 1) (hb : d126843 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d94493, d126843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27784 q ha hb
    | true =>
      simp only [d94493, d126843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94494 q = 1) (hb : d126844 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d94494, d126844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94494, d126844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94495 q = 1) (hb : d126845 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d94495, d126845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94495, d126845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94496 q = 1) (hb : d126846 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d94496, d126846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94496, d126846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94497 q = 1) (hb : d126847 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d94497, d126847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94497, d126847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94498 q = 1) (hb : d126848 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d94498, d126848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94498, d126848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27786 (p : Pattern) (ha : d94504 p = 1) (hb : d126854 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94499 q = 1) (hb : d126849 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d94499, d126849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27785 q ha hb
    | true =>
      simp only [d94499, d126849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94500 q = 1) (hb : d126850 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d94500, d126850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94500, d126850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94501 q = 1) (hb : d126851 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d94501, d126851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94501, d126851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94502 q = 1) (hb : d126852 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d94502, d126852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94502, d126852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94503 q = 1) (hb : d126853 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d94503, d126853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94503, d126853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94504 q = 1) (hb : d126854 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d94504, d126854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94504, d126854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27787 (p : Pattern) (ha : d94510 p = 1) (hb : d126860 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94505 q = 1) (hb : d126855 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d94505, d126855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27786 q ha hb
    | true =>
      simp only [d94505, d126855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94506 q = 1) (hb : d126856 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d94506, d126856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94506, d126856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94507 q = 1) (hb : d126857 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d94507, d126857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94507, d126857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94508 q = 1) (hb : d126858 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d94508, d126858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94508, d126858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94509 q = 1) (hb : d126859 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d94509, d126859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94509, d126859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94510 q = 1) (hb : d126860 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d94510, d126860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94510, d126860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27788 (p : Pattern) (ha : d94516 p = 1) (hb : d126866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d94511 q = 1) (hb : d126861 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d94511, d126861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27787 q ha hb
    | true =>
      simp only [d94511, d126861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d94512 q = 1) (hb : d126862 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d94512, d126862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94512, d126862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d94513 q = 1) (hb : d126863 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d94513, d126863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94513, d126863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d94514 q = 1) (hb : d126864 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d94514, d126864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94514, d126864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94515 q = 1) (hb : d126865 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d94515, d126865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94515, d126865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d94516 q = 1) (hb : d126866 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d94516, d126866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94516, d126866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27789 (p : Pattern) (ha : d107485 p = 1) (hb : d109109 p = 1) : d109109 p = 1 := by
  have h0 (q : Pattern) (ha : d107485 q = 1) (hb : d109109 q = 1) : d109109 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro27790 (p : Pattern) (ha : d107485 p = 1) (hb : d109322 p = 1) : d109322 p = 1 := by
  have h0 (q : Pattern) (ha : d107485 q = 1) (hb : d109322 q = 1) : d109322 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro27791 (p : Pattern) (ha : d144 p = 1) (hb : d146836 p = 1) : d148547 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d139 q = 1) (hb : d116750 q = 1) : d751 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19799 q ha hb
    | true =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d140 q = 1) (hb : d116750 q = 1) : d752 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d141 q = 1) (hb : d116750 q = 1) : d753 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d142 q = 1) (hb : d116750 q = 1) : d754 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d142, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d116750 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d143 q = 1) (hb : d116750 q = 1) : d20892 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d143, d20892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d143, d20892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d29 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d144 q = 1) (hb : d146836 q = 1) : d148547 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d144, d146836, d148547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144, d146836, d148547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro27792 (p : Pattern) (ha : d10654 p = 1) (hb : d146837 p = 1) : d148553 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10649 q = 1) (hb : d146837 q = 1) : d148548 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d146837, d148548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27791 q ha hb
    | true =>
      simp only [d10649, d146837, d148548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10650 q = 1) (hb : d146837 q = 1) : d148549 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d148549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10650, d148549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10651 q = 1) (hb : d146837 q = 1) : d148550 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d148550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10651, d148550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d146837 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10652 q = 1) (hb : d146837 q = 1) : d148551 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10652, d148551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10652, d148551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d146837 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10653 q = 1) (hb : d146837 q = 1) : d148552 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10653, d148552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10653, d148552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10654 q = 1) (hb : d146837 q = 1) : d148553 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10654, d148553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10654, d148553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro27793 (p : Pattern) (ha : d10660 p = 1) (hb : d146837 p = 1) : d148559 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d146837 q = 1) : d148554 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27792 q ha hb
    | true =>
      simp only [d10655, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d146837 q = 1) : d148555 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d146837 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10657 q = 1) (hb : d146837 q = 1) : d148556 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d148556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d148556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10658 q = 1) (hb : d146837 q = 1) : d148557 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, d148557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10658, d148557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10659 q = 1) (hb : d146837 q = 1) : d148558 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10659, d148558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10659, d148558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10660 q = 1) (hb : d146837 q = 1) : d148559 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10660, d148559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10660, d148559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro27794 (p : Pattern) (ha : d108784 p = 1) (hb : d146837 p = 1) : d148565 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d146837 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d146837 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d146837 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10661 q = 1) (hb : d146837 q = 1) : d148560 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d148560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27793 q ha hb
    | true =>
      simp only [d10661, d148560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108780 q = 1) (hb : d146837 q = 1) : d148561 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108780, d148561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108780, d148561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d146837 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108781 q = 1) (hb : d146837 q = 1) : d148562 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108781, d148562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108781, d148562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108782 q = 1) (hb : d146837 q = 1) : d148563 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108782, d148563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108782, d148563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108783 q = 1) (hb : d146837 q = 1) : d148564 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108783, d148564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108783, d148564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108784 q = 1) (hb : d146837 q = 1) : d148565 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108784, d148565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108784, d148565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro27795 (p : Pattern) (ha : d10667 p = 1) (hb : d146837 p = 1) : d148566 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d146837 q = 1) : d148554 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27792 q ha hb
    | true =>
      simp only [d10655, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d146837 q = 1) : d148555 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d146837 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10657 q = 1) (hb : d146837 q = 1) : d148556 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d148556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d148556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10658 q = 1) (hb : d146837 q = 1) : d148557 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, d148557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10658, d148557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10659 q = 1) (hb : d146837 q = 1) : d148558 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10659, d148558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10659, d148558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10667 q = 1) (hb : d146837 q = 1) : d148566 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10667, d148566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10667, d148566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro27796 (p : Pattern) (ha : d108789 p = 1) (hb : d146837 p = 1) : d148572 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d146837 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d146837 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d146837 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10661 q = 1) (hb : d146837 q = 1) : d148560 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d148560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27793 q ha hb
    | true =>
      simp only [d10661, d148560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108780 q = 1) (hb : d146837 q = 1) : d148561 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108780, d148561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108780, d148561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d146837 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108781 q = 1) (hb : d146837 q = 1) : d148562 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108781, d148562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108781, d148562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108782 q = 1) (hb : d146837 q = 1) : d148563 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108782, d148563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108782, d148563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108783 q = 1) (hb : d146837 q = 1) : d148564 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108783, d148564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108783, d148564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d146837 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d146837 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d146837 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d10668 q = 1) (hb : d146837 q = 1) : d148567 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10668, d148567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27795 q ha hb
    | true =>
      simp only [d10668, d148567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108785 q = 1) (hb : d146837 q = 1) : d148568 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108785, d148568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108785, d148568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d146837 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d108786 q = 1) (hb : d146837 q = 1) : d148569 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108786, d148569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108786, d148569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108787 q = 1) (hb : d146837 q = 1) : d148570 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108787, d148570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108787, d148570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108788 q = 1) (hb : d146837 q = 1) : d148571 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108788, d148571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108788, d148571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d108789 q = 1) (hb : d146837 q = 1) : d148572 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108789, d148572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108789, d148572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro27797 (p : Pattern) (ha : d108796 p = 1) (hb : d146837 p = 1) : d148579 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d146837 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10668 q = 1) (hb : d146837 q = 1) : d148567 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10668, d148567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27795 q ha hb
    | true =>
      simp only [d10668, d148567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108785 q = 1) (hb : d146837 q = 1) : d148568 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108785, d148568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108785, d148568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d146837 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108786 q = 1) (hb : d146837 q = 1) : d148569 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108786, d148569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108786, d148569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108794 q = 1) (hb : d146837 q = 1) : d148577 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108794, d148577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108794, d148577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108795 q = 1) (hb : d146837 q = 1) : d148578 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108795, d148578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108795, d148578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108796 q = 1) (hb : d146837 q = 1) : d148579 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108796, d148579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108796, d148579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27798 (p : Pattern) (ha : d231 p = 1) (hb : d146836 p = 1) : d148585 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d226 q = 1) (hb : d116750 q = 1) : d971 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19799 q ha hb
  have h2 (q : Pattern) (ha : d139 q = 1) (hb : d116750 q = 1) : d751 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19799 q ha hb
    | true =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d227 q = 1) (hb : d116750 q = 1) : d972 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d227, d972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d140 q = 1) (hb : d116750 q = 1) : d752 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d228 q = 1) (hb : d116750 q = 1) : d973 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d228, d973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d229 q = 1) (hb : d116750 q = 1) : d974 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d229, d974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d116750 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d230 q = 1) (hb : d116750 q = 1) : d20931 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d230, d20931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d230, d20931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d70 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d231 q = 1) (hb : d146836 q = 1) : d148585 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231, d146836, d148585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d231, d146836, d148585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro27799 (p : Pattern) (ha : d10691 p = 1) (hb : d146837 p = 1) : d148591 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10686 q = 1) (hb : d146837 q = 1) : d148586 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d146837, d148586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27798 q ha hb
    | true =>
      simp only [d10686, d146837, d148586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10687 q = 1) (hb : d146837 q = 1) : d148587 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d148587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10687, d148587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10688 q = 1) (hb : d146837 q = 1) : d148588 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d148588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10688, d148588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d146837 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10689 q = 1) (hb : d146837 q = 1) : d148589 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10689, d148589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10689, d148589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d146837 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10690 q = 1) (hb : d146837 q = 1) : d148590 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10690, d148590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10690, d148590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10691 q = 1) (hb : d146837 q = 1) : d148591 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10691, d148591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10691, d148591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro27800 (p : Pattern) (ha : d10697 p = 1) (hb : d146837 p = 1) : d148597 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10692 q = 1) (hb : d146837 q = 1) : d148592 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10692, d148592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27799 q ha hb
    | true =>
      simp only [d10692, d148592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10693 q = 1) (hb : d146837 q = 1) : d148593 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10693, d148593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10693, d148593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d146837 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10694 q = 1) (hb : d146837 q = 1) : d148594 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10694, d148594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10694, d148594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10695 q = 1) (hb : d146837 q = 1) : d148595 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10695, d148595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10695, d148595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10696 q = 1) (hb : d146837 q = 1) : d148596 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10696, d148596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10696, d148596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10697 q = 1) (hb : d146837 q = 1) : d148597 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10697, d148597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10697, d148597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro27801 (p : Pattern) (ha : d108806 p = 1) (hb : d146837 p = 1) : d148603 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d146837 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10698 q = 1) (hb : d146837 q = 1) : d148598 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10698, d148598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27800 q ha hb
    | true =>
      simp only [d10698, d148598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108802 q = 1) (hb : d146837 q = 1) : d148599 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108802, d148599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108802, d148599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d146837 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108803 q = 1) (hb : d146837 q = 1) : d148600 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108803, d148600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108803, d148600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108804 q = 1) (hb : d146837 q = 1) : d148601 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108804, d148601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108804, d148601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108805 q = 1) (hb : d146837 q = 1) : d148602 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108805, d148602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108805, d148602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108806 q = 1) (hb : d146837 q = 1) : d148603 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108806, d148603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108806, d148603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27802 (p : Pattern) (ha : d108812 p = 1) (hb : d146837 p = 1) : d148609 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d146837 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108790 q = 1) (hb : d146837 q = 1) : d148573 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108790, d148573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27794 q ha hb
    | true =>
      simp only [d108790, d148573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27796 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d146837 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108791 q = 1) (hb : d146837 q = 1) : d148574 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108791, d148574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108791, d148574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108792 q = 1) (hb : d146837 q = 1) : d148575 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108792, d148575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108792, d148575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108793 q = 1) (hb : d146837 q = 1) : d148576 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108793, d148576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108793, d148576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108797 q = 1) (hb : d146837 q = 1) : d148580 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108797, d148580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108797, d148580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27797 q ha hb
  have h8 (q : Pattern) (ha : d108798 q = 1) (hb : d146837 q = 1) : d148581 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108798, d148581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108798, d148581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d108799 q = 1) (hb : d146837 q = 1) : d148582 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108799, d148582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108799, d148582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d108800 q = 1) (hb : d146837 q = 1) : d148583 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108800, d148583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108800, d148583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d108801 q = 1) (hb : d146837 q = 1) : d148584 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108801, d148584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108801, d148584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d108807 q = 1) (hb : d146837 q = 1) : d148604 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108807, d148604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108807, d148604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27801 q ha hb
  have h13 (q : Pattern) (ha : d108808 q = 1) (hb : d146837 q = 1) : d148605 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108808, d148605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108808, d148605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d108809 q = 1) (hb : d146837 q = 1) : d148606 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108809, d148606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108809, d148606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d108810 q = 1) (hb : d146837 q = 1) : d148607 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108810, d148607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108810, d148607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d108811 q = 1) (hb : d146837 q = 1) : d148608 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108811, d148608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108811, d148608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d108812 q = 1) (hb : d146837 q = 1) : d148609 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108812, d148609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108812, d148609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro27803 (p : Pattern) (ha : d10719 p = 1) (hb : d146837 p = 1) : d148619 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d146837 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10661 q = 1) (hb : d146837 q = 1) : d148560 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d148560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27793 q ha hb
    | true =>
      simp only [d10661, d148560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10715 q = 1) (hb : d146837 q = 1) : d148615 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10715, d148615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10715, d148615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10716 q = 1) (hb : d146837 q = 1) : d148616 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10716, d148616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10716, d148616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10717 q = 1) (hb : d146837 q = 1) : d148617 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10717, d148617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10717, d148617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10718 q = 1) (hb : d146837 q = 1) : d148618 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10718, d148618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10718, d148618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10719 q = 1) (hb : d146837 q = 1) : d148619 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10719, d148619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10719, d148619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro27804 (p : Pattern) (ha : d10726 p = 1) (hb : d146837 p = 1) : d148626 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d146837 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10661 q = 1) (hb : d146837 q = 1) : d148560 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d148560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27793 q ha hb
    | true =>
      simp only [d10661, d148560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10715 q = 1) (hb : d146837 q = 1) : d148615 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10715, d148615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10715, d148615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10716 q = 1) (hb : d146837 q = 1) : d148616 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10716, d148616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10716, d148616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10717 q = 1) (hb : d146837 q = 1) : d148617 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10717, d148617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10717, d148617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10718 q = 1) (hb : d146837 q = 1) : d148618 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10718, d148618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10718, d148618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d146837 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10668 q = 1) (hb : d146837 q = 1) : d148567 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10668, d148567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27795 q ha hb
    | true =>
      simp only [d10668, d148567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10722 q = 1) (hb : d146837 q = 1) : d148622 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10722, d148622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10722, d148622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10723 q = 1) (hb : d146837 q = 1) : d148623 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10723, d148623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10723, d148623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10724 q = 1) (hb : d146837 q = 1) : d148624 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10724, d148624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10724, d148624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10725 q = 1) (hb : d146837 q = 1) : d148625 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10725, d148625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10725, d148625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10726 q = 1) (hb : d146837 q = 1) : d148626 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10726, d148626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10726, d148626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro27805 (p : Pattern) (ha : d10801 p = 1) (hb : d146837 p = 1) : d148687 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d146837 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10661 q = 1) (hb : d146837 q = 1) : d148560 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d148560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27793 q ha hb
    | true =>
      simp only [d10661, d148560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10715 q = 1) (hb : d146837 q = 1) : d148615 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10715, d148615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10715, d148615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10716 q = 1) (hb : d146837 q = 1) : d148616 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10716, d148616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10716, d148616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10717 q = 1) (hb : d146837 q = 1) : d148617 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10717, d148617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10717, d148617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10718 q = 1) (hb : d146837 q = 1) : d148618 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10718, d148618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10718, d148618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d146837 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10801 q = 1) (hb : d146837 q = 1) : d148687 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10801, d148687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10801, d148687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27806 (p : Pattern) (ha : d10731 p = 1) (hb : d146837 p = 1) : d148631 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d146837 q = 1) : d148554 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27792 q ha hb
    | true =>
      simp only [d10655, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d146837 q = 1) : d148555 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d146837 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10657 q = 1) (hb : d146837 q = 1) : d148556 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d148556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d148556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10658 q = 1) (hb : d146837 q = 1) : d148557 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, d148557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10658, d148557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10730 q = 1) (hb : d146837 q = 1) : d148630 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10730, d148630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10730, d148630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10731 q = 1) (hb : d146837 q = 1) : d148631 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10731, d148631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10731, d148631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro27807 (p : Pattern) (ha : d10738 p = 1) (hb : d146837 p = 1) : d148638 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d146837 q = 1) : d148554 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27792 q ha hb
    | true =>
      simp only [d10655, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d146837 q = 1) : d148555 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d146837 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10657 q = 1) (hb : d146837 q = 1) : d148556 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d148556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d148556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10736 q = 1) (hb : d146837 q = 1) : d148636 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10736, d148636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10736, d148636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10737 q = 1) (hb : d146837 q = 1) : d148637 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10737, d148637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10737, d148637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10738 q = 1) (hb : d146837 q = 1) : d148638 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10738, d148638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10738, d148638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro27808 (p : Pattern) (ha : d324 p = 1) (hb : d146836 p = 1) : d148642 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d116750 q = 1) : d20990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
    | true =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d320 q = 1) (hb : d116750 q = 1) : d20991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321 q = 1) (hb : d116750 q = 1) : d20992 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d20992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d20992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d116750 q = 1) : d20993 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d20993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322, d20993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d139 q = 1) (hb : d116750 q = 1) : d751 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19799 q ha hb
    | true =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d140 q = 1) (hb : d116750 q = 1) : d752 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d141 q = 1) (hb : d116750 q = 1) : d753 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d142 q = 1) (hb : d116750 q = 1) : d754 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d142, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d323 q = 1) (hb : d116750 q = 1) : d20994 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d323, d20994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d323, d20994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d143 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d324 q = 1) (hb : d146836 q = 1) : d148642 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d324, d146836, d148642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d324, d146836, d148642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro27809 (p : Pattern) (ha : d10747 p = 1) (hb : d146837 p = 1) : d148648 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10742 q = 1) (hb : d146837 q = 1) : d148643 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10742, d146837, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27808 q ha hb
    | true =>
      simp only [d10742, d146837, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10743 q = 1) (hb : d146837 q = 1) : d148644 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10743, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10743, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10744 q = 1) (hb : d146837 q = 1) : d148645 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10744, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10744, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10649 q = 1) (hb : d146837 q = 1) : d148548 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d146837, d148548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27791 q ha hb
    | true =>
      simp only [d10649, d146837, d148548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d10650 q = 1) (hb : d146837 q = 1) : d148549 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d148549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10650, d148549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10651 q = 1) (hb : d146837 q = 1) : d148550 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d148550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10651, d148550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10745 q = 1) (hb : d146837 q = 1) : d148646 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10745, d148646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10745, d148646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d146837 q = 1) : d33 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d10652 q = 1) (hb : d146837 q = 1) : d148551 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10652, d148551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10652, d148551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10746 q = 1) (hb : d146837 q = 1) : d148647 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10746, d148647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10746, d148647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10747 q = 1) (hb : d146837 q = 1) : d148648 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10747, d148648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10747, d148648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro27810 (p : Pattern) (ha : d10753 p = 1) (hb : d146837 p = 1) : d148654 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10748 q = 1) (hb : d146837 q = 1) : d148649 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10748, d148649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27809 q ha hb
    | true =>
      simp only [d10748, d148649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10749 q = 1) (hb : d146837 q = 1) : d148650 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10749, d148650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10749, d148650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10655 q = 1) (hb : d146837 q = 1) : d148554 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27792 q ha hb
    | true =>
      simp only [d10655, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10656 q = 1) (hb : d146837 q = 1) : d148555 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10750 q = 1) (hb : d146837 q = 1) : d148651 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10750, d148651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10750, d148651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10751 q = 1) (hb : d146837 q = 1) : d148652 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10751, d148652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10751, d148652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10752 q = 1) (hb : d146837 q = 1) : d148653 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10752, d148653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10752, d148653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10753 q = 1) (hb : d146837 q = 1) : d148654 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10753, d148654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10753, d148654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27811 (p : Pattern) (ha : d10772 p = 1) (hb : d146837 p = 1) : d148660 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d146837 q = 1) : d148554 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27792 q ha hb
    | true =>
      simp only [d10655, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d146837 q = 1) : d148555 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10769 q = 1) (hb : d146837 q = 1) : d148657 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10769, d148657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10769, d148657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10770 q = 1) (hb : d146837 q = 1) : d148658 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10770, d148658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10770, d148658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10771 q = 1) (hb : d146837 q = 1) : d148659 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10771, d148659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10771, d148659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10772 q = 1) (hb : d146837 q = 1) : d148660 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10772, d148660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10772, d148660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27812 (p : Pattern) (ha : d108822 p = 1) (hb : d146837 p = 1) : d148666 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d146837 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10732 q = 1) (hb : d146837 q = 1) : d148632 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10732, d148632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27806 q ha hb
    | true =>
      simp only [d10732, d148632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10733 q = 1) (hb : d146837 q = 1) : d148633 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10733, d148633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10733, d148633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10734 q = 1) (hb : d146837 q = 1) : d148634 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10734, d148634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10734, d148634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10735 q = 1) (hb : d146837 q = 1) : d148635 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10735, d148635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10735, d148635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d146837 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10739 q = 1) (hb : d146837 q = 1) : d148639 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10739, d148639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27807 q ha hb
    | true =>
      simp only [d10739, d148639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10740 q = 1) (hb : d146837 q = 1) : d148640 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10740, d148640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10740, d148640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10741 q = 1) (hb : d146837 q = 1) : d148641 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10741, d148641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10741, d148641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10754 q = 1) (hb : d146837 q = 1) : d148655 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10754, d148655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27810 q ha hb
    | true =>
      simp only [d10754, d148655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27793 q ha hb
  have h11 (q : Pattern) (ha : d108818 q = 1) (hb : d146837 q = 1) : d148656 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108818, d148656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108818, d148656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10773 q = 1) (hb : d146837 q = 1) : d148661 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10773, d148661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27811 q ha hb
    | true =>
      simp only [d10773, d148661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d10774 q = 1) (hb : d146837 q = 1) : d148662 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10774, d148662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10774, d148662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d108819 q = 1) (hb : d146837 q = 1) : d148663 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108819, d148663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108819, d148663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108820 q = 1) (hb : d146837 q = 1) : d148664 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108820, d148664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108820, d148664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108821 q = 1) (hb : d146837 q = 1) : d148665 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108821, d148665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108821, d148665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108822 q = 1) (hb : d146837 q = 1) : d148666 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108822, d148666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108822, d148666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro27813 (p : Pattern) (ha : d10779 p = 1) (hb : d146837 p = 1) : d148667 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d146837 q = 1) : d148554 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27792 q ha hb
    | true =>
      simp only [d10655, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d146837 q = 1) : d148555 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d146837 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10657 q = 1) (hb : d146837 q = 1) : d148556 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d148556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d148556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10658 q = 1) (hb : d146837 q = 1) : d148557 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, d148557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10658, d148557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10730 q = 1) (hb : d146837 q = 1) : d148630 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10730, d148630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10730, d148630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10779 q = 1) (hb : d146837 q = 1) : d148667 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10779, d148667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10779, d148667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro27814 (p : Pattern) (ha : d10784 p = 1) (hb : d146837 p = 1) : d148672 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d146837 q = 1) : d148554 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27792 q ha hb
    | true =>
      simp only [d10655, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d146837 q = 1) : d148555 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d146837 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10657 q = 1) (hb : d146837 q = 1) : d148556 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d148556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d148556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10736 q = 1) (hb : d146837 q = 1) : d148636 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10736, d148636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10736, d148636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10737 q = 1) (hb : d146837 q = 1) : d148637 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10737, d148637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10737, d148637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10784 q = 1) (hb : d146837 q = 1) : d148672 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10784, d148672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10784, d148672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro27815 (p : Pattern) (ha : d10788 p = 1) (hb : d146837 p = 1) : d148676 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10748 q = 1) (hb : d146837 q = 1) : d148649 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10748, d148649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27809 q ha hb
    | true =>
      simp only [d10748, d148649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10749 q = 1) (hb : d146837 q = 1) : d148650 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10749, d148650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10749, d148650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10655 q = 1) (hb : d146837 q = 1) : d148554 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27792 q ha hb
    | true =>
      simp only [d10655, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10656 q = 1) (hb : d146837 q = 1) : d148555 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10750 q = 1) (hb : d146837 q = 1) : d148651 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10750, d148651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10750, d148651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10751 q = 1) (hb : d146837 q = 1) : d148652 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10751, d148652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10751, d148652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10752 q = 1) (hb : d146837 q = 1) : d148653 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10752, d148653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10752, d148653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10788 q = 1) (hb : d146837 q = 1) : d148676 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10788, d148676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10788, d148676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27816 (p : Pattern) (ha : d10793 p = 1) (hb : d146837 p = 1) : d148679 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d146837 q = 1) : d148554 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27792 q ha hb
    | true =>
      simp only [d10655, d148554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d146837 q = 1) : d148555 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d148555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10769 q = 1) (hb : d146837 q = 1) : d148657 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10769, d148657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10769, d148657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10770 q = 1) (hb : d146837 q = 1) : d148658 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10770, d148658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10770, d148658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10771 q = 1) (hb : d146837 q = 1) : d148659 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10771, d148659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10771, d148659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10793 q = 1) (hb : d146837 q = 1) : d148679 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10793, d148679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10793, d148679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27817 (p : Pattern) (ha : d108827 p = 1) (hb : d146837 p = 1) : d148685 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d146837 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10732 q = 1) (hb : d146837 q = 1) : d148632 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10732, d148632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27806 q ha hb
    | true =>
      simp only [d10732, d148632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10733 q = 1) (hb : d146837 q = 1) : d148633 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10733, d148633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10733, d148633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10734 q = 1) (hb : d146837 q = 1) : d148634 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10734, d148634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10734, d148634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10735 q = 1) (hb : d146837 q = 1) : d148635 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10735, d148635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10735, d148635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d146837 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10739 q = 1) (hb : d146837 q = 1) : d148639 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10739, d148639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27807 q ha hb
    | true =>
      simp only [d10739, d148639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10740 q = 1) (hb : d146837 q = 1) : d148640 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10740, d148640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10740, d148640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10741 q = 1) (hb : d146837 q = 1) : d148641 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10741, d148641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10741, d148641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10754 q = 1) (hb : d146837 q = 1) : d148655 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10754, d148655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27810 q ha hb
    | true =>
      simp only [d10754, d148655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27793 q ha hb
  have h11 (q : Pattern) (ha : d108818 q = 1) (hb : d146837 q = 1) : d148656 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108818, d148656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108818, d148656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10773 q = 1) (hb : d146837 q = 1) : d148661 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10773, d148661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27811 q ha hb
    | true =>
      simp only [d10773, d148661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d10774 q = 1) (hb : d146837 q = 1) : d148662 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10774, d148662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10774, d148662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d108819 q = 1) (hb : d146837 q = 1) : d148663 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108819, d148663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108819, d148663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108820 q = 1) (hb : d146837 q = 1) : d148664 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108820, d148664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108820, d148664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108821 q = 1) (hb : d146837 q = 1) : d148665 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108821, d148665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108821, d148665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d146837 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d10780 q = 1) (hb : d146837 q = 1) : d148668 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10780, d148668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27813 q ha hb
    | true =>
      simp only [d10780, d148668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10781 q = 1) (hb : d146837 q = 1) : d148669 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10781, d148669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10781, d148669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10782 q = 1) (hb : d146837 q = 1) : d148670 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10782, d148670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10782, d148670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d10783 q = 1) (hb : d146837 q = 1) : d148671 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10783, d148671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10783, d148671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d146837 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d10785 q = 1) (hb : d146837 q = 1) : d148673 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10785, d148673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27814 q ha hb
    | true =>
      simp only [d10785, d148673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d10786 q = 1) (hb : d146837 q = 1) : d148674 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10786, d148674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10786, d148674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d10787 q = 1) (hb : d146837 q = 1) : d148675 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10787, d148675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d10787, d148675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d10789 q = 1) (hb : d146837 q = 1) : d148677 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10789, d148677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27815 q ha hb
    | true =>
      simp only [d10789, d148677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27795 q ha hb
  have h27 (q : Pattern) (ha : d108823 q = 1) (hb : d146837 q = 1) : d148678 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108823, d148678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d108823, d148678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d10794 q = 1) (hb : d146837 q = 1) : d148680 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10794, d148680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27816 q ha hb
    | true =>
      simp only [d10794, d148680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d10795 q = 1) (hb : d146837 q = 1) : d148681 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10795, d148681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d10795, d148681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d108824 q = 1) (hb : d146837 q = 1) : d148682 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108824, d148682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d108824, d148682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d108825 q = 1) (hb : d146837 q = 1) : d148683 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108825, d148683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d108825, d148683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d108826 q = 1) (hb : d146837 q = 1) : d148684 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108826, d148684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108826, d148684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d108827 q = 1) (hb : d146837 q = 1) : d148685 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108827, d148685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108827, d148685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro27818 (p : Pattern) (ha : d108834 p = 1) (hb : d146837 p = 1) : d148694 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10789 q = 1) (hb : d146837 q = 1) : d148677 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10789, d148677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27815 q ha hb
    | true =>
      simp only [d10789, d148677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27795 q ha hb
  have h2 (q : Pattern) (ha : d108823 q = 1) (hb : d146837 q = 1) : d148678 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108823, d148678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108823, d148678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10794 q = 1) (hb : d146837 q = 1) : d148680 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10794, d148680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27816 q ha hb
    | true =>
      simp only [d10794, d148680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10795 q = 1) (hb : d146837 q = 1) : d148681 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10795, d148681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10795, d148681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108824 q = 1) (hb : d146837 q = 1) : d148682 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108824, d148682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108824, d148682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108832 q = 1) (hb : d146837 q = 1) : d148692 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108832, d148692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108832, d148692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108833 q = 1) (hb : d146837 q = 1) : d148693 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108833, d148693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108833, d148693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108834 q = 1) (hb : d146837 q = 1) : d148694 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108834, d148694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108834, d148694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27819 (p : Pattern) (ha : d417 p = 1) (hb : d146836 p = 1) : d148700 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d412 q = 1) (hb : d116750 q = 1) : d21071 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d21071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d21071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d116750 q = 1) : d20990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
    | true =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d413 q = 1) (hb : d116750 q = 1) : d21072 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d21072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d413, d21072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320 q = 1) (hb : d116750 q = 1) : d20991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d414 q = 1) (hb : d116750 q = 1) : d21073 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d21073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d414, d21073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d415 q = 1) (hb : d116750 q = 1) : d21074 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d21074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d415, d21074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d226 q = 1) (hb : d116750 q = 1) : d971 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19799 q ha hb
  have h8 (q : Pattern) (ha : d139 q = 1) (hb : d116750 q = 1) : d751 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19799 q ha hb
    | true =>
      simp only [d139, d751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d227 q = 1) (hb : d116750 q = 1) : d972 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d227, d972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d140 q = 1) (hb : d116750 q = 1) : d752 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d140, d752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d228 q = 1) (hb : d116750 q = 1) : d973 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d228, d973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d229 q = 1) (hb : d116750 q = 1) : d974 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d229, d974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d416 q = 1) (hb : d116750 q = 1) : d21075 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d416, d21075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d416, d21075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d230 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d417 q = 1) (hb : d146836 q = 1) : d148700 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d417, d146836, d148700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d417, d146836, d148700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro27820 (p : Pattern) (ha : d10819 p = 1) (hb : d146837 p = 1) : d148706 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10814 q = 1) (hb : d146837 q = 1) : d148701 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10814, d146837, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27819 q ha hb
    | true =>
      simp only [d10814, d146837, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10815 q = 1) (hb : d146837 q = 1) : d148702 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10815, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10815, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10816 q = 1) (hb : d146837 q = 1) : d148703 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10816, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10816, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10686 q = 1) (hb : d146837 q = 1) : d148586 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d146837, d148586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27798 q ha hb
    | true =>
      simp only [d10686, d146837, d148586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d10687 q = 1) (hb : d146837 q = 1) : d148587 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d148587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10687, d148587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10688 q = 1) (hb : d146837 q = 1) : d148588 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d148588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10688, d148588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10817 q = 1) (hb : d146837 q = 1) : d148704 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10817, d148704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10817, d148704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d146837 q = 1) : d74 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d10689 q = 1) (hb : d146837 q = 1) : d148589 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10689, d148589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10689, d148589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10818 q = 1) (hb : d146837 q = 1) : d148705 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10818, d148705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10818, d148705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10819 q = 1) (hb : d146837 q = 1) : d148706 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10819, d148706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10819, d148706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro27821 (p : Pattern) (ha : d10825 p = 1) (hb : d146837 p = 1) : d148712 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10820 q = 1) (hb : d146837 q = 1) : d148707 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10820, d148707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27820 q ha hb
    | true =>
      simp only [d10820, d148707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10821 q = 1) (hb : d146837 q = 1) : d148708 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10821, d148708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10821, d148708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10692 q = 1) (hb : d146837 q = 1) : d148592 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10692, d148592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27799 q ha hb
    | true =>
      simp only [d10692, d148592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10693 q = 1) (hb : d146837 q = 1) : d148593 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10693, d148593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10693, d148593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10822 q = 1) (hb : d146837 q = 1) : d148709 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10822, d148709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10822, d148709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10823 q = 1) (hb : d146837 q = 1) : d148710 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10823, d148710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10823, d148710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10824 q = 1) (hb : d146837 q = 1) : d148711 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10824, d148711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10824, d148711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10825 q = 1) (hb : d146837 q = 1) : d148712 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10825, d148712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10825, d148712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27822 (p : Pattern) (ha : d10844 p = 1) (hb : d146837 p = 1) : d148718 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10692 q = 1) (hb : d146837 q = 1) : d148592 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10692, d148592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27799 q ha hb
    | true =>
      simp only [d10692, d148592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10693 q = 1) (hb : d146837 q = 1) : d148593 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10693, d148593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10693, d148593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10841 q = 1) (hb : d146837 q = 1) : d148715 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10841, d148715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10841, d148715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10842 q = 1) (hb : d146837 q = 1) : d148716 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10842, d148716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10842, d148716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10843 q = 1) (hb : d146837 q = 1) : d148717 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10843, d148717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10843, d148717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10844 q = 1) (hb : d146837 q = 1) : d148718 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10844, d148718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10844, d148718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27823 (p : Pattern) (ha : d108844 p = 1) (hb : d146837 p = 1) : d148724 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10826 q = 1) (hb : d146837 q = 1) : d148713 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10826, d148713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27821 q ha hb
    | true =>
      simp only [d10826, d148713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27800 q ha hb
  have h2 (q : Pattern) (ha : d108840 q = 1) (hb : d146837 q = 1) : d148714 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108840, d148714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108840, d148714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10845 q = 1) (hb : d146837 q = 1) : d148719 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10845, d148719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27822 q ha hb
    | true =>
      simp only [d10845, d148719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10846 q = 1) (hb : d146837 q = 1) : d148720 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10846, d148720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10846, d148720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108841 q = 1) (hb : d146837 q = 1) : d148721 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108841, d148721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108841, d148721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108842 q = 1) (hb : d146837 q = 1) : d148722 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108842, d148722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108842, d148722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108843 q = 1) (hb : d146837 q = 1) : d148723 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108843, d148723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108843, d148723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108844 q = 1) (hb : d146837 q = 1) : d148724 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108844, d148724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108844, d148724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27824 (p : Pattern) (ha : d108850 p = 1) (hb : d146837 p = 1) : d148730 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10720 q = 1) (hb : d146837 q = 1) : d148620 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10720, d148620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10720, d148620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27803 q ha hb
  have h2 (q : Pattern) (ha : d10721 q = 1) (hb : d146837 q = 1) : d148621 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10721, d148621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10721, d148621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10727 q = 1) (hb : d146837 q = 1) : d148627 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10727, d148627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27803 q ha hb
    | true =>
      simp only [d10727, d148627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27804 q ha hb
  have h4 (q : Pattern) (ha : d10728 q = 1) (hb : d146837 q = 1) : d148628 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10728, d148628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10728, d148628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10729 q = 1) (hb : d146837 q = 1) : d148629 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d10729, d148629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10729, d148629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108828 q = 1) (hb : d146837 q = 1) : d148686 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108828, d148686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27812 q ha hb
    | true =>
      simp only [d108828, d148686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27817 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d146837 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10802 q = 1) (hb : d146837 q = 1) : d148688 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10802, d148688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27805 q ha hb
    | true =>
      simp only [d10802, d148688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108829 q = 1) (hb : d146837 q = 1) : d148689 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108829, d148689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108829, d148689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108830 q = 1) (hb : d146837 q = 1) : d148690 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108830, d148690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108830, d148690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d108831 q = 1) (hb : d146837 q = 1) : d148691 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108831, d148691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108831, d148691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d108835 q = 1) (hb : d146837 q = 1) : d148695 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108835, d148695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108835, d148695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27818 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d146837 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d108836 q = 1) (hb : d146837 q = 1) : d148696 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108836, d148696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108836, d148696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108837 q = 1) (hb : d146837 q = 1) : d148697 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108837, d148697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108837, d148697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d108838 q = 1) (hb : d146837 q = 1) : d148698 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108838, d148698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108838, d148698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d108839 q = 1) (hb : d146837 q = 1) : d148699 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108839, d148699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108839, d148699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108845 q = 1) (hb : d146837 q = 1) : d148725 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108845, d148725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108845, d148725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27823 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d146837 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d108846 q = 1) (hb : d146837 q = 1) : d148726 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108846, d148726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d108846, d148726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d108847 q = 1) (hb : d146837 q = 1) : d148727 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108847, d148727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d108847, d148727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d108848 q = 1) (hb : d146837 q = 1) : d148728 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108848, d148728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108848, d148728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d108849 q = 1) (hb : d146837 q = 1) : d148729 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108849, d148729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d108849, d148729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d108850 q = 1) (hb : d146837 q = 1) : d148730 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108850, d148730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108850, d148730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro27825 (p : Pattern) (ha : d108856 p = 1) (hb : d146837 p = 1) : d148736 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d146837 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108813 q = 1) (hb : d146837 q = 1) : d148610 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108813, d148610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108813, d148610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27802 q ha hb
  have h3 (q : Pattern) (ha : d108814 q = 1) (hb : d146837 q = 1) : d148611 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108814, d148611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108814, d148611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108815 q = 1) (hb : d146837 q = 1) : d148612 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108815, d148612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108815, d148612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108816 q = 1) (hb : d146837 q = 1) : d148613 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108816, d148613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108816, d148613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108817 q = 1) (hb : d146837 q = 1) : d148614 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108817, d148614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108817, d148614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108851 q = 1) (hb : d146837 q = 1) : d148731 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108851, d148731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108851, d148731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27824 q ha hb
  have h8 (q : Pattern) (ha : d108852 q = 1) (hb : d146837 q = 1) : d148732 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108852, d148732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108852, d148732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108853 q = 1) (hb : d146837 q = 1) : d148733 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108853, d148733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108853, d148733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108854 q = 1) (hb : d146837 q = 1) : d148734 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108854, d148734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108854, d148734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108855 q = 1) (hb : d146837 q = 1) : d148735 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108855, d148735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108855, d148735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d108856 q = 1) (hb : d146837 q = 1) : d148736 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108856, d148736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108856, d148736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro27826 (p : Pattern) (ha : d10865 p = 1) (hb : d146837 p = 1) : d148739 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10742 q = 1) (hb : d146837 q = 1) : d148643 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10742, d146837, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27808 q ha hb
    | true =>
      simp only [d10742, d146837, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10743 q = 1) (hb : d146837 q = 1) : d148644 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10743, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10743, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10744 q = 1) (hb : d146837 q = 1) : d148645 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10744, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10744, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10649 q = 1) (hb : d146837 q = 1) : d148548 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d146837, d148548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27791 q ha hb
    | true =>
      simp only [d10649, d146837, d148548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d10650 q = 1) (hb : d146837 q = 1) : d148549 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d148549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10650, d148549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10651 q = 1) (hb : d146837 q = 1) : d148550 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d148550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10651, d148550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10745 q = 1) (hb : d146837 q = 1) : d148646 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10745, d148646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10745, d148646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10863 q = 1) (hb : d146837 q = 1) : d148737 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10863, d148737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10863, d148737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10864 q = 1) (hb : d146837 q = 1) : d148738 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10864, d148738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10864, d148738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10865 q = 1) (hb : d146837 q = 1) : d148739 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10865, d148739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10865, d148739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro27827 (p : Pattern) (ha : d10869 p = 1) (hb : d146837 p = 1) : d148743 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10649 q = 1) (hb : d146837 q = 1) : d148548 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d146837, d148548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27791 q ha hb
    | true =>
      simp only [d10649, d146837, d148548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10650 q = 1) (hb : d146837 q = 1) : d148549 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d148549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10650, d148549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10651 q = 1) (hb : d146837 q = 1) : d148550 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d148550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10651, d148550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10863 q = 1) (hb : d146837 q = 1) : d148737 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10863, d148737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10863, d148737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10868 q = 1) (hb : d146837 q = 1) : d148742 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10868, d148742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10868, d148742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10869 q = 1) (hb : d146837 q = 1) : d148743 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10869, d148743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10869, d148743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro27828 (p : Pattern) (ha : d10875 p = 1) (hb : d146837 p = 1) : d148749 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d146837 q = 1) : d148740 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27826 q ha hb
    | true =>
      simp only [d10866, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d146837 q = 1) : d148741 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d146837 q = 1) : d148744 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27827 q ha hb
    | true =>
      simp only [d10870, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d146837 q = 1) : d148745 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10872 q = 1) (hb : d146837 q = 1) : d148746 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d148746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d148746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10873 q = 1) (hb : d146837 q = 1) : d148747 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10873, d148747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10873, d148747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10874 q = 1) (hb : d146837 q = 1) : d148748 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10874, d148748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10874, d148748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10875 q = 1) (hb : d146837 q = 1) : d148749 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10875, d148749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10875, d148749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27829 (p : Pattern) (ha : d10879 p = 1) (hb : d146837 p = 1) : d148753 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10870 q = 1) (hb : d146837 q = 1) : d148744 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27827 q ha hb
    | true =>
      simp only [d10870, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10871 q = 1) (hb : d146837 q = 1) : d148745 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10876 q = 1) (hb : d146837 q = 1) : d148750 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d148750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10876, d148750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10877 q = 1) (hb : d146837 q = 1) : d148751 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10877, d148751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10877, d148751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10878 q = 1) (hb : d146837 q = 1) : d148752 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10878, d148752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10878, d148752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10879 q = 1) (hb : d146837 q = 1) : d148753 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10879, d148753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10879, d148753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27830 (p : Pattern) (ha : d10885 p = 1) (hb : d146837 p = 1) : d148759 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10880 q = 1) (hb : d146837 q = 1) : d148754 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10880, d148754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27828 q ha hb
    | true =>
      simp only [d10880, d148754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27829 q ha hb
  have h2 (q : Pattern) (ha : d10881 q = 1) (hb : d146837 q = 1) : d148755 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10881, d148755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10881, d148755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10882 q = 1) (hb : d146837 q = 1) : d148756 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10882, d148756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10882, d148756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10883 q = 1) (hb : d146837 q = 1) : d148757 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10883, d148757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10883, d148757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10884 q = 1) (hb : d146837 q = 1) : d148758 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10884, d148758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10884, d148758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10885 q = 1) (hb : d146837 q = 1) : d148759 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10885, d148759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10885, d148759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27831 (p : Pattern) (ha : d10888 p = 1) (hb : d146837 p = 1) : d148762 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d146837 q = 1) : d148740 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27826 q ha hb
    | true =>
      simp only [d10866, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d146837 q = 1) : d148741 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d146837 q = 1) : d148744 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27827 q ha hb
    | true =>
      simp only [d10870, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d146837 q = 1) : d148745 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10872 q = 1) (hb : d146837 q = 1) : d148746 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d148746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d148746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10873 q = 1) (hb : d146837 q = 1) : d148747 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10873, d148747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10873, d148747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10874 q = 1) (hb : d146837 q = 1) : d148748 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10874, d148748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10874, d148748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10888 q = 1) (hb : d146837 q = 1) : d148762 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10888, d148762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10888, d148762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27832 (p : Pattern) (ha : d10889 p = 1) (hb : d146837 p = 1) : d148763 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10870 q = 1) (hb : d146837 q = 1) : d148744 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27827 q ha hb
    | true =>
      simp only [d10870, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10871 q = 1) (hb : d146837 q = 1) : d148745 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10876 q = 1) (hb : d146837 q = 1) : d148750 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d148750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10876, d148750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10877 q = 1) (hb : d146837 q = 1) : d148751 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10877, d148751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10877, d148751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10878 q = 1) (hb : d146837 q = 1) : d148752 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10878, d148752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10878, d148752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10889 q = 1) (hb : d146837 q = 1) : d148763 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10889, d148763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10889, d148763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27833 (p : Pattern) (ha : d10895 p = 1) (hb : d146837 p = 1) : d148769 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10880 q = 1) (hb : d146837 q = 1) : d148754 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10880, d148754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27828 q ha hb
    | true =>
      simp only [d10880, d148754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27829 q ha hb
  have h2 (q : Pattern) (ha : d10881 q = 1) (hb : d146837 q = 1) : d148755 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10881, d148755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10881, d148755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10882 q = 1) (hb : d146837 q = 1) : d148756 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10882, d148756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10882, d148756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10883 q = 1) (hb : d146837 q = 1) : d148757 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10883, d148757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10883, d148757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10884 q = 1) (hb : d146837 q = 1) : d148758 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10884, d148758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10884, d148758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10890 q = 1) (hb : d146837 q = 1) : d148764 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10890, d148764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27831 q ha hb
    | true =>
      simp only [d10890, d148764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27832 q ha hb
  have h7 (q : Pattern) (ha : d10891 q = 1) (hb : d146837 q = 1) : d148765 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10891, d148765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10891, d148765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10892 q = 1) (hb : d146837 q = 1) : d148766 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10892, d148766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10892, d148766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d10893 q = 1) (hb : d146837 q = 1) : d148767 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10893, d148767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10893, d148767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10894 q = 1) (hb : d146837 q = 1) : d148768 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10894, d148768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10894, d148768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10895 q = 1) (hb : d146837 q = 1) : d148769 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10895, d148769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10895, d148769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27834 (p : Pattern) (ha : d10992 p = 1) (hb : d146837 p = 1) : d148842 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10880 q = 1) (hb : d146837 q = 1) : d148754 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10880, d148754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27828 q ha hb
    | true =>
      simp only [d10880, d148754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27829 q ha hb
  have h2 (q : Pattern) (ha : d10881 q = 1) (hb : d146837 q = 1) : d148755 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10881, d148755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10881, d148755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10882 q = 1) (hb : d146837 q = 1) : d148756 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10882, d148756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10882, d148756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10883 q = 1) (hb : d146837 q = 1) : d148757 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10883, d148757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10883, d148757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10884 q = 1) (hb : d146837 q = 1) : d148758 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10884, d148758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10884, d148758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10987 q = 1) (hb : d146837 q = 1) : d148837 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10987, d148837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27829 q ha hb
    | true =>
      simp only [d10987, d148837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10988 q = 1) (hb : d146837 q = 1) : d148838 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10988, d148838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10988, d148838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10989 q = 1) (hb : d146837 q = 1) : d148839 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10989, d148839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10989, d148839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d10990 q = 1) (hb : d146837 q = 1) : d148840 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10990, d148840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10990, d148840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10991 q = 1) (hb : d146837 q = 1) : d148841 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10991, d148841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10991, d148841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10992 q = 1) (hb : d146837 q = 1) : d148842 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10992, d148842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10992, d148842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27835 (p : Pattern) (ha : d10998 p = 1) (hb : d146837 p = 1) : d148848 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10987 q = 1) (hb : d146837 q = 1) : d148837 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10987, d148837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27829 q ha hb
    | true =>
      simp only [d10987, d148837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10988 q = 1) (hb : d146837 q = 1) : d148838 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10988, d148838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10988, d148838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10989 q = 1) (hb : d146837 q = 1) : d148839 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10989, d148839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10989, d148839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10990 q = 1) (hb : d146837 q = 1) : d148840 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10990, d148840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10990, d148840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10991 q = 1) (hb : d146837 q = 1) : d148841 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10991, d148841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10991, d148841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10993 q = 1) (hb : d146837 q = 1) : d148843 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10993, d148843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27832 q ha hb
    | true =>
      simp only [d10993, d148843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10994 q = 1) (hb : d146837 q = 1) : d148844 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10994, d148844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10994, d148844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10995 q = 1) (hb : d146837 q = 1) : d148845 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10995, d148845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10995, d148845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d10996 q = 1) (hb : d146837 q = 1) : d148846 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10996, d148846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10996, d148846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10997 q = 1) (hb : d146837 q = 1) : d148847 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10997, d148847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10997, d148847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10998 q = 1) (hb : d146837 q = 1) : d148848 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10998, d148848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10998, d148848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27836 (p : Pattern) (ha : d11007 p = 1) (hb : d146837 p = 1) : d148857 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10993 q = 1) (hb : d146837 q = 1) : d148843 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10993, d148843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27832 q ha hb
    | true =>
      simp only [d10993, d148843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10994 q = 1) (hb : d146837 q = 1) : d148844 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10994, d148844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10994, d148844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10995 q = 1) (hb : d146837 q = 1) : d148845 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10995, d148845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10995, d148845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10996 q = 1) (hb : d146837 q = 1) : d148846 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10996, d148846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10996, d148846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10997 q = 1) (hb : d146837 q = 1) : d148847 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10997, d148847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10997, d148847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11007 q = 1) (hb : d146837 q = 1) : d148857 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11007, d148857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11007, d148857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27837 (p : Pattern) (ha : d11031 p = 1) (hb : d146837 p = 1) : d148882 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10686 q = 1) (hb : d146837 q = 1) : d148586 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d146837, d148586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27798 q ha hb
    | true =>
      simp only [d10686, d146837, d148586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10687 q = 1) (hb : d146837 q = 1) : d148587 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d148587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10687, d148587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10688 q = 1) (hb : d146837 q = 1) : d148588 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d148588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10688, d148588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11021 q = 1) (hb : d146837 q = 1) : d148872 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11021, d148872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11021, d148872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11030 q = 1) (hb : d146837 q = 1) : d148881 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11030, d148881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11030, d148881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11031 q = 1) (hb : d146837 q = 1) : d148882 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11031, d148882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11031, d148882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro27838 (p : Pattern) (ha : d11076 p = 1) (hb : d146837 p = 1) : d148905 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11032 q = 1) (hb : d146837 q = 1) : d148883 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11032, d148883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27837 q ha hb
    | true =>
      simp only [d11032, d148883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11033 q = 1) (hb : d146837 q = 1) : d148884 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11033, d148884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11033, d148884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11073 q = 1) (hb : d146837 q = 1) : d148902 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11073, d148902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11073, d148902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11074 q = 1) (hb : d146837 q = 1) : d148903 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11074, d148903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11074, d148903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11075 q = 1) (hb : d146837 q = 1) : d148904 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11075, d148904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11075, d148904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11076 q = 1) (hb : d146837 q = 1) : d148905 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11076, d148905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11076, d148905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27839 (p : Pattern) (ha : d11082 p = 1) (hb : d146837 p = 1) : d148911 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11077 q = 1) (hb : d146837 q = 1) : d148906 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11077, d148906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27838 q ha hb
    | true =>
      simp only [d11077, d148906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11078 q = 1) (hb : d146837 q = 1) : d148907 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11078, d148907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11078, d148907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11079 q = 1) (hb : d146837 q = 1) : d148908 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11079, d148908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11079, d148908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11080 q = 1) (hb : d146837 q = 1) : d148909 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11080, d148909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11080, d148909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11081 q = 1) (hb : d146837 q = 1) : d148910 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11081, d148910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11081, d148910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11082 q = 1) (hb : d146837 q = 1) : d148911 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11082, d148911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11082, d148911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27840 (p : Pattern) (ha : d10900 p = 1) (hb : d146837 p = 1) : d148774 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d146837 q = 1) : d148740 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27826 q ha hb
    | true =>
      simp only [d10866, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d146837 q = 1) : d148741 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d146837 q = 1) : d148744 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27827 q ha hb
    | true =>
      simp only [d10870, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d146837 q = 1) : d148745 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10872 q = 1) (hb : d146837 q = 1) : d148746 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d148746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d148746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10873 q = 1) (hb : d146837 q = 1) : d148747 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10873, d148747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10873, d148747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10899 q = 1) (hb : d146837 q = 1) : d148773 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10899, d148773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10899, d148773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10900 q = 1) (hb : d146837 q = 1) : d148774 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10900, d148774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10900, d148774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27841 (p : Pattern) (ha : d10902 p = 1) (hb : d146837 p = 1) : d148776 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10870 q = 1) (hb : d146837 q = 1) : d148744 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27827 q ha hb
    | true =>
      simp only [d10870, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10871 q = 1) (hb : d146837 q = 1) : d148745 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10876 q = 1) (hb : d146837 q = 1) : d148750 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d148750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10876, d148750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10877 q = 1) (hb : d146837 q = 1) : d148751 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10877, d148751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10877, d148751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10901 q = 1) (hb : d146837 q = 1) : d148775 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10901, d148775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10901, d148775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10902 q = 1) (hb : d146837 q = 1) : d148776 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10902, d148776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10902, d148776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27842 (p : Pattern) (ha : d10909 p = 1) (hb : d146837 p = 1) : d148783 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d146837 q = 1) : d148740 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27826 q ha hb
    | true =>
      simp only [d10866, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d146837 q = 1) : d148741 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d146837 q = 1) : d148744 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27827 q ha hb
    | true =>
      simp only [d10870, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d146837 q = 1) : d148745 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10872 q = 1) (hb : d146837 q = 1) : d148746 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d148746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d148746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10907 q = 1) (hb : d146837 q = 1) : d148781 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10907, d148781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10907, d148781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10908 q = 1) (hb : d146837 q = 1) : d148782 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10908, d148782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10908, d148782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10909 q = 1) (hb : d146837 q = 1) : d148783 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10909, d148783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10909, d148783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27843 (p : Pattern) (ha : d10912 p = 1) (hb : d146837 p = 1) : d148786 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10870 q = 1) (hb : d146837 q = 1) : d148744 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27827 q ha hb
    | true =>
      simp only [d10870, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10871 q = 1) (hb : d146837 q = 1) : d148745 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10876 q = 1) (hb : d146837 q = 1) : d148750 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d148750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10876, d148750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10910 q = 1) (hb : d146837 q = 1) : d148784 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10910, d148784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10910, d148784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10911 q = 1) (hb : d146837 q = 1) : d148785 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10911, d148785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10911, d148785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10912 q = 1) (hb : d146837 q = 1) : d148786 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10912, d148786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10912, d148786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27844 (p : Pattern) (ha : d548 p = 1) (hb : d146836 p = 1) : d148790 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d543 q = 1) (hb : d116750 q = 1) : d21183 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19889 q ha hb
    | true =>
      simp only [d543, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d544 q = 1) (hb : d116750 q = 1) : d21184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d544, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d545 q = 1) (hb : d116750 q = 1) : d21185 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d545, d21185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d545, d21185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d546 q = 1) (hb : d116750 q = 1) : d21186 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d546, d21186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d546, d21186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d319 q = 1) (hb : d116750 q = 1) : d20990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
    | true =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d320 q = 1) (hb : d116750 q = 1) : d20991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d321 q = 1) (hb : d116750 q = 1) : d20992 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d20992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d20992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d322 q = 1) (hb : d116750 q = 1) : d20993 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d20993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d322, d20993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d547 q = 1) (hb : d116750 q = 1) : d21187 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d547, d21187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d547, d21187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d323 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d548 q = 1) (hb : d146836 q = 1) : d148790 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d548, d146836, d148790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d548, d146836, d148790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro27845 (p : Pattern) (ha : d10921 p = 1) (hb : d146837 p = 1) : d148796 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10916 q = 1) (hb : d146837 q = 1) : d148791 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10916, d146837, d148791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27844 q ha hb
    | true =>
      simp only [d10916, d146837, d148791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10917 q = 1) (hb : d146837 q = 1) : d148792 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10917, d148792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10917, d148792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10918 q = 1) (hb : d146837 q = 1) : d148793 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10918, d148793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10918, d148793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10742 q = 1) (hb : d146837 q = 1) : d148643 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10742, d146837, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27808 q ha hb
    | true =>
      simp only [d10742, d146837, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d10743 q = 1) (hb : d146837 q = 1) : d148644 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10743, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10743, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10744 q = 1) (hb : d146837 q = 1) : d148645 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10744, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10744, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10919 q = 1) (hb : d146837 q = 1) : d148794 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10919, d148794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10919, d148794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10649 q = 1) (hb : d146837 q = 1) : d148548 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d146837, d148548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27791 q ha hb
    | true =>
      simp only [d10649, d146837, d148548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d10650 q = 1) (hb : d146837 q = 1) : d148549 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d148549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10650, d148549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10651 q = 1) (hb : d146837 q = 1) : d148550 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d148550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10651, d148550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10745 q = 1) (hb : d146837 q = 1) : d148646 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10745, d148646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10745, d148646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10920 q = 1) (hb : d146837 q = 1) : d148795 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10920, d148795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10920, d148795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10921 q = 1) (hb : d146837 q = 1) : d148796 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10921, d148796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10921, d148796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro27846 (p : Pattern) (ha : d10927 p = 1) (hb : d146837 p = 1) : d148802 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10922 q = 1) (hb : d146837 q = 1) : d148797 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10922, d148797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27845 q ha hb
    | true =>
      simp only [d10922, d148797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10923 q = 1) (hb : d146837 q = 1) : d148798 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10923, d148798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10923, d148798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10866 q = 1) (hb : d146837 q = 1) : d148740 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27826 q ha hb
    | true =>
      simp only [d10866, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10867 q = 1) (hb : d146837 q = 1) : d148741 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10924 q = 1) (hb : d146837 q = 1) : d148799 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10924, d148799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10924, d148799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10925 q = 1) (hb : d146837 q = 1) : d148800 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10925, d148800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10925, d148800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10926 q = 1) (hb : d146837 q = 1) : d148801 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10926, d148801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10926, d148801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10927 q = 1) (hb : d146837 q = 1) : d148802 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10927, d148802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10927, d148802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27847 (p : Pattern) (ha : d10955 p = 1) (hb : d146837 p = 1) : d148808 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d146837 q = 1) : d148740 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27826 q ha hb
    | true =>
      simp only [d10866, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d146837 q = 1) : d148741 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10952 q = 1) (hb : d146837 q = 1) : d148805 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10952, d148805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10952, d148805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10953 q = 1) (hb : d146837 q = 1) : d148806 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10953, d148806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10953, d148806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10954 q = 1) (hb : d146837 q = 1) : d148807 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10954, d148807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10954, d148807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10955 q = 1) (hb : d146837 q = 1) : d148808 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10955, d148808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10955, d148808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27848 (p : Pattern) (ha : d108861 p = 1) (hb : d146837 p = 1) : d148814 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10903 q = 1) (hb : d146837 q = 1) : d148777 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10903, d148777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27840 q ha hb
    | true =>
      simp only [d10903, d148777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27841 q ha hb
  have h2 (q : Pattern) (ha : d10904 q = 1) (hb : d146837 q = 1) : d148778 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10904, d148778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10904, d148778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10905 q = 1) (hb : d146837 q = 1) : d148779 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10905, d148779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10905, d148779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10906 q = 1) (hb : d146837 q = 1) : d148780 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10906, d148780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10906, d148780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10913 q = 1) (hb : d146837 q = 1) : d148787 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10913, d148787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27842 q ha hb
    | true =>
      simp only [d10913, d148787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27843 q ha hb
  have h6 (q : Pattern) (ha : d10914 q = 1) (hb : d146837 q = 1) : d148788 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10914, d148788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10914, d148788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10915 q = 1) (hb : d146837 q = 1) : d148789 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10915, d148789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10915, d148789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10928 q = 1) (hb : d146837 q = 1) : d148803 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10928, d148803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27846 q ha hb
    | true =>
      simp only [d10928, d148803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27828 q ha hb
  have h9 (q : Pattern) (ha : d108857 q = 1) (hb : d146837 q = 1) : d148804 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108857, d148804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108857, d148804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10956 q = 1) (hb : d146837 q = 1) : d148809 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10956, d148809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27847 q ha hb
    | true =>
      simp only [d10956, d148809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10957 q = 1) (hb : d146837 q = 1) : d148810 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10957, d148810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10957, d148810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d108858 q = 1) (hb : d146837 q = 1) : d148811 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108858, d148811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108858, d148811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108859 q = 1) (hb : d146837 q = 1) : d148812 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108859, d148812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108859, d148812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108860 q = 1) (hb : d146837 q = 1) : d148813 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108860, d148813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108860, d148813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108861 q = 1) (hb : d146837 q = 1) : d148814 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108861, d148814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108861, d148814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro27849 (p : Pattern) (ha : d10962 p = 1) (hb : d146837 p = 1) : d148815 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d146837 q = 1) : d148740 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27826 q ha hb
    | true =>
      simp only [d10866, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d146837 q = 1) : d148741 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d146837 q = 1) : d148744 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27827 q ha hb
    | true =>
      simp only [d10870, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d146837 q = 1) : d148745 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10872 q = 1) (hb : d146837 q = 1) : d148746 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d148746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d148746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10873 q = 1) (hb : d146837 q = 1) : d148747 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10873, d148747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10873, d148747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10899 q = 1) (hb : d146837 q = 1) : d148773 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10899, d148773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10899, d148773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10962 q = 1) (hb : d146837 q = 1) : d148815 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10962, d148815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10962, d148815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27850 (p : Pattern) (ha : d10963 p = 1) (hb : d146837 p = 1) : d148816 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10870 q = 1) (hb : d146837 q = 1) : d148744 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27827 q ha hb
    | true =>
      simp only [d10870, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10871 q = 1) (hb : d146837 q = 1) : d148745 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10876 q = 1) (hb : d146837 q = 1) : d148750 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d148750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10876, d148750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10877 q = 1) (hb : d146837 q = 1) : d148751 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10877, d148751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10877, d148751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10901 q = 1) (hb : d146837 q = 1) : d148775 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10901, d148775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10901, d148775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10963 q = 1) (hb : d146837 q = 1) : d148816 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10963, d148816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10963, d148816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27851 (p : Pattern) (ha : d10968 p = 1) (hb : d146837 p = 1) : d148821 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d146837 q = 1) : d148740 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27826 q ha hb
    | true =>
      simp only [d10866, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d146837 q = 1) : d148741 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d146837 q = 1) : d148744 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27827 q ha hb
    | true =>
      simp only [d10870, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d146837 q = 1) : d148745 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10872 q = 1) (hb : d146837 q = 1) : d148746 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d148746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d148746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10907 q = 1) (hb : d146837 q = 1) : d148781 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10907, d148781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10907, d148781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10908 q = 1) (hb : d146837 q = 1) : d148782 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10908, d148782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10908, d148782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10968 q = 1) (hb : d146837 q = 1) : d148821 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10968, d148821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10968, d148821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27852 (p : Pattern) (ha : d10969 p = 1) (hb : d146837 p = 1) : d148822 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10870 q = 1) (hb : d146837 q = 1) : d148744 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27827 q ha hb
    | true =>
      simp only [d10870, d148744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10871 q = 1) (hb : d146837 q = 1) : d148745 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d148745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10876 q = 1) (hb : d146837 q = 1) : d148750 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d148750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10876, d148750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10910 q = 1) (hb : d146837 q = 1) : d148784 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10910, d148784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10910, d148784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10911 q = 1) (hb : d146837 q = 1) : d148785 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10911, d148785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10911, d148785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10969 q = 1) (hb : d146837 q = 1) : d148822 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10969, d148822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10969, d148822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27853 (p : Pattern) (ha : d10973 p = 1) (hb : d146837 p = 1) : d148826 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10922 q = 1) (hb : d146837 q = 1) : d148797 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10922, d148797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27845 q ha hb
    | true =>
      simp only [d10922, d148797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10923 q = 1) (hb : d146837 q = 1) : d148798 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10923, d148798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10923, d148798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10866 q = 1) (hb : d146837 q = 1) : d148740 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27826 q ha hb
    | true =>
      simp only [d10866, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10867 q = 1) (hb : d146837 q = 1) : d148741 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10924 q = 1) (hb : d146837 q = 1) : d148799 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10924, d148799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10924, d148799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10925 q = 1) (hb : d146837 q = 1) : d148800 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10925, d148800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10925, d148800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10926 q = 1) (hb : d146837 q = 1) : d148801 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10926, d148801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10926, d148801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10973 q = 1) (hb : d146837 q = 1) : d148826 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10973, d148826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10973, d148826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27854 (p : Pattern) (ha : d10979 p = 1) (hb : d146837 p = 1) : d148829 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d146837 q = 1) : d148740 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27826 q ha hb
    | true =>
      simp only [d10866, d148740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d146837 q = 1) : d148741 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d148741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10952 q = 1) (hb : d146837 q = 1) : d148805 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10952, d148805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10952, d148805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10953 q = 1) (hb : d146837 q = 1) : d148806 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10953, d148806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10953, d148806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10954 q = 1) (hb : d146837 q = 1) : d148807 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10954, d148807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10954, d148807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10979 q = 1) (hb : d146837 q = 1) : d148829 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10979, d148829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10979, d148829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27855 (p : Pattern) (ha : d108866 p = 1) (hb : d146837 p = 1) : d148835 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10903 q = 1) (hb : d146837 q = 1) : d148777 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10903, d148777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27840 q ha hb
    | true =>
      simp only [d10903, d148777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27841 q ha hb
  have h2 (q : Pattern) (ha : d10904 q = 1) (hb : d146837 q = 1) : d148778 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10904, d148778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10904, d148778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10905 q = 1) (hb : d146837 q = 1) : d148779 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10905, d148779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10905, d148779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10906 q = 1) (hb : d146837 q = 1) : d148780 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10906, d148780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10906, d148780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10913 q = 1) (hb : d146837 q = 1) : d148787 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10913, d148787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27842 q ha hb
    | true =>
      simp only [d10913, d148787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27843 q ha hb
  have h6 (q : Pattern) (ha : d10914 q = 1) (hb : d146837 q = 1) : d148788 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10914, d148788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10914, d148788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10915 q = 1) (hb : d146837 q = 1) : d148789 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10915, d148789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10915, d148789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10928 q = 1) (hb : d146837 q = 1) : d148803 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10928, d148803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27846 q ha hb
    | true =>
      simp only [d10928, d148803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27828 q ha hb
  have h9 (q : Pattern) (ha : d108857 q = 1) (hb : d146837 q = 1) : d148804 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108857, d148804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108857, d148804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10956 q = 1) (hb : d146837 q = 1) : d148809 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10956, d148809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27847 q ha hb
    | true =>
      simp only [d10956, d148809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10957 q = 1) (hb : d146837 q = 1) : d148810 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10957, d148810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10957, d148810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d108858 q = 1) (hb : d146837 q = 1) : d148811 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108858, d148811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108858, d148811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108859 q = 1) (hb : d146837 q = 1) : d148812 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108859, d148812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108859, d148812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108860 q = 1) (hb : d146837 q = 1) : d148813 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108860, d148813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108860, d148813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d10964 q = 1) (hb : d146837 q = 1) : d148817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10964, d148817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27849 q ha hb
    | true =>
      simp only [d10964, d148817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27850 q ha hb
  have h16 (q : Pattern) (ha : d10965 q = 1) (hb : d146837 q = 1) : d148818 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10965, d148818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10965, d148818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10966 q = 1) (hb : d146837 q = 1) : d148819 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10966, d148819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10966, d148819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d10967 q = 1) (hb : d146837 q = 1) : d148820 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10967, d148820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10967, d148820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10970 q = 1) (hb : d146837 q = 1) : d148823 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10970, d148823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27851 q ha hb
    | true =>
      simp only [d10970, d148823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27852 q ha hb
  have h20 (q : Pattern) (ha : d10971 q = 1) (hb : d146837 q = 1) : d148824 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10971, d148824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10971, d148824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d10972 q = 1) (hb : d146837 q = 1) : d148825 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10972, d148825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d10972, d148825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d10974 q = 1) (hb : d146837 q = 1) : d148827 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10974, d148827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27853 q ha hb
    | true =>
      simp only [d10974, d148827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27831 q ha hb
  have h23 (q : Pattern) (ha : d108862 q = 1) (hb : d146837 q = 1) : d148828 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108862, d148828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d108862, d148828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d10980 q = 1) (hb : d146837 q = 1) : d148830 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10980, d148830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27854 q ha hb
    | true =>
      simp only [d10980, d148830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d10981 q = 1) (hb : d146837 q = 1) : d148831 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10981, d148831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d10981, d148831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d108863 q = 1) (hb : d146837 q = 1) : d148832 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108863, d148832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d108863, d148832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d108864 q = 1) (hb : d146837 q = 1) : d148833 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108864, d148833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108864, d148833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d108865 q = 1) (hb : d146837 q = 1) : d148834 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108865, d148834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d108865, d148834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d108866 q = 1) (hb : d146837 q = 1) : d148835 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108866, d148835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108866, d148835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro27856 (p : Pattern) (ha : d108873 p = 1) (hb : d146837 p = 1) : d148855 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10974 q = 1) (hb : d146837 q = 1) : d148827 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10974, d148827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27853 q ha hb
    | true =>
      simp only [d10974, d148827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27831 q ha hb
  have h2 (q : Pattern) (ha : d108862 q = 1) (hb : d146837 q = 1) : d148828 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108862, d148828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108862, d148828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10980 q = 1) (hb : d146837 q = 1) : d148830 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10980, d148830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27854 q ha hb
    | true =>
      simp only [d10980, d148830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10981 q = 1) (hb : d146837 q = 1) : d148831 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10981, d148831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10981, d148831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108863 q = 1) (hb : d146837 q = 1) : d148832 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108863, d148832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108863, d148832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108871 q = 1) (hb : d146837 q = 1) : d148853 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108871, d148853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108871, d148853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108872 q = 1) (hb : d146837 q = 1) : d148854 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108872, d148854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108872, d148854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108873 q = 1) (hb : d146837 q = 1) : d148855 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108873, d148855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108873, d148855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27857 (p : Pattern) (ha : d664 p = 1) (hb : d146836 p = 1) : d148863 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d659 q = 1) (hb : d116750 q = 1) : d21309 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d659, d21309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d659, d21309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19889 q ha hb
  have h2 (q : Pattern) (ha : d543 q = 1) (hb : d116750 q = 1) : d21183 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19889 q ha hb
    | true =>
      simp only [d543, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d660 q = 1) (hb : d116750 q = 1) : d21310 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, d21310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d660, d21310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d544 q = 1) (hb : d116750 q = 1) : d21184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d544, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d661 q = 1) (hb : d116750 q = 1) : d21311 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d661, d21311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d661, d21311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d662 q = 1) (hb : d116750 q = 1) : d21312 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d662, d21312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d662, d21312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d412 q = 1) (hb : d116750 q = 1) : d21071 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d21071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d21071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
  have h8 (q : Pattern) (ha : d319 q = 1) (hb : d116750 q = 1) : d20990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
    | true =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d413 q = 1) (hb : d116750 q = 1) : d21072 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d21072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d413, d21072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d320 q = 1) (hb : d116750 q = 1) : d20991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d414 q = 1) (hb : d116750 q = 1) : d21073 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d21073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d414, d21073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d415 q = 1) (hb : d116750 q = 1) : d21074 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d21074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d415, d21074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d663 q = 1) (hb : d116750 q = 1) : d21313 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d663, d21313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d663, d21313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d416 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d664 q = 1) (hb : d146836 q = 1) : d148863 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d664, d146836, d148863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d664, d146836, d148863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro27858 (p : Pattern) (ha : d11018 p = 1) (hb : d146837 p = 1) : d148869 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11013 q = 1) (hb : d146837 q = 1) : d148864 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11013, d146837, d148864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27857 q ha hb
    | true =>
      simp only [d11013, d146837, d148864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11014 q = 1) (hb : d146837 q = 1) : d148865 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11014, d148865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11014, d148865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11015 q = 1) (hb : d146837 q = 1) : d148866 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11015, d148866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11015, d148866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10814 q = 1) (hb : d146837 q = 1) : d148701 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10814, d146837, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27819 q ha hb
    | true =>
      simp only [d10814, d146837, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d10815 q = 1) (hb : d146837 q = 1) : d148702 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10815, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10815, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10816 q = 1) (hb : d146837 q = 1) : d148703 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10816, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10816, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11016 q = 1) (hb : d146837 q = 1) : d148867 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11016, d148867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11016, d148867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10686 q = 1) (hb : d146837 q = 1) : d148586 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d146837, d148586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27798 q ha hb
    | true =>
      simp only [d10686, d146837, d148586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d10687 q = 1) (hb : d146837 q = 1) : d148587 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d148587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10687, d148587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10688 q = 1) (hb : d146837 q = 1) : d148588 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d148588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10688, d148588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10817 q = 1) (hb : d146837 q = 1) : d148704 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10817, d148704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10817, d148704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11017 q = 1) (hb : d146837 q = 1) : d148868 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11017, d148868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11017, d148868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11018 q = 1) (hb : d146837 q = 1) : d148869 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11018, d148869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11018, d148869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro27859 (p : Pattern) (ha : d11023 p = 1) (hb : d146837 p = 1) : d148874 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10814 q = 1) (hb : d146837 q = 1) : d148701 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10814, d146837, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27819 q ha hb
    | true =>
      simp only [d10814, d146837, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10815 q = 1) (hb : d146837 q = 1) : d148702 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10815, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10815, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10816 q = 1) (hb : d146837 q = 1) : d148703 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10816, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10816, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10686 q = 1) (hb : d146837 q = 1) : d148586 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d146837, d148586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27798 q ha hb
    | true =>
      simp only [d10686, d146837, d148586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d10687 q = 1) (hb : d146837 q = 1) : d148587 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d148587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10687, d148587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10688 q = 1) (hb : d146837 q = 1) : d148588 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d148588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10688, d148588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10817 q = 1) (hb : d146837 q = 1) : d148704 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10817, d148704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10817, d148704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11021 q = 1) (hb : d146837 q = 1) : d148872 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11021, d148872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11021, d148872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11022 q = 1) (hb : d146837 q = 1) : d148873 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11022, d148873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11022, d148873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11023 q = 1) (hb : d146837 q = 1) : d148874 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11023, d148874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11023, d148874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro27860 (p : Pattern) (ha : d11029 p = 1) (hb : d146837 p = 1) : d148880 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11019 q = 1) (hb : d146837 q = 1) : d148870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11019, d148870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27858 q ha hb
    | true =>
      simp only [d11019, d148870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11020 q = 1) (hb : d146837 q = 1) : d148871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11020, d148871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11020, d148871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11024 q = 1) (hb : d146837 q = 1) : d148875 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11024, d148875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27859 q ha hb
    | true =>
      simp only [d11024, d148875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11025 q = 1) (hb : d146837 q = 1) : d148876 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11025, d148876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11025, d148876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11026 q = 1) (hb : d146837 q = 1) : d148877 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11026, d148877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11026, d148877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11027 q = 1) (hb : d146837 q = 1) : d148878 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11027, d148878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11027, d148878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11028 q = 1) (hb : d146837 q = 1) : d148879 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11028, d148879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11028, d148879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11029 q = 1) (hb : d146837 q = 1) : d148880 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11029, d148880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11029, d148880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27861 (p : Pattern) (ha : d11037 p = 1) (hb : d146837 p = 1) : d148888 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11024 q = 1) (hb : d146837 q = 1) : d148875 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11024, d148875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27859 q ha hb
    | true =>
      simp only [d11024, d148875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11025 q = 1) (hb : d146837 q = 1) : d148876 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11025, d148876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11025, d148876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11032 q = 1) (hb : d146837 q = 1) : d148883 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11032, d148883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27837 q ha hb
    | true =>
      simp only [d11032, d148883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11033 q = 1) (hb : d146837 q = 1) : d148884 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11033, d148884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11033, d148884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11034 q = 1) (hb : d146837 q = 1) : d148885 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11034, d148885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11034, d148885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11035 q = 1) (hb : d146837 q = 1) : d148886 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11035, d148886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11035, d148886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11036 q = 1) (hb : d146837 q = 1) : d148887 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11036, d148887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11036, d148887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11037 q = 1) (hb : d146837 q = 1) : d148888 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11037, d148888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11037, d148888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27862 (p : Pattern) (ha : d11065 p = 1) (hb : d146837 p = 1) : d148894 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11024 q = 1) (hb : d146837 q = 1) : d148875 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11024, d148875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27859 q ha hb
    | true =>
      simp only [d11024, d148875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11025 q = 1) (hb : d146837 q = 1) : d148876 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11025, d148876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11025, d148876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11062 q = 1) (hb : d146837 q = 1) : d148891 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11062, d148891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11062, d148891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11063 q = 1) (hb : d146837 q = 1) : d148892 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11063, d148892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11063, d148892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11064 q = 1) (hb : d146837 q = 1) : d148893 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11064, d148893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11064, d148893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11065 q = 1) (hb : d146837 q = 1) : d148894 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11065, d148894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11065, d148894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27863 (p : Pattern) (ha : d108883 p = 1) (hb : d146837 p = 1) : d148900 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11038 q = 1) (hb : d146837 q = 1) : d148889 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11038, d148889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27860 q ha hb
    | true =>
      simp only [d11038, d148889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27861 q ha hb
  have h2 (q : Pattern) (ha : d108879 q = 1) (hb : d146837 q = 1) : d148890 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108879, d148890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108879, d148890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11066 q = 1) (hb : d146837 q = 1) : d148895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11066, d148895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27862 q ha hb
    | true =>
      simp only [d11066, d148895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11067 q = 1) (hb : d146837 q = 1) : d148896 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11067, d148896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11067, d148896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108880 q = 1) (hb : d146837 q = 1) : d148897 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108880, d148897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108880, d148897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108881 q = 1) (hb : d146837 q = 1) : d148898 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108881, d148898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108881, d148898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108882 q = 1) (hb : d146837 q = 1) : d148899 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108882, d148899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108882, d148899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108883 q = 1) (hb : d146837 q = 1) : d148900 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108883, d148900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108883, d148900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27864 (p : Pattern) (ha : d108889 p = 1) (hb : d146837 p = 1) : d148917 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10886 q = 1) (hb : d146837 q = 1) : d148760 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10886, d148760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10886, d148760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27830 q ha hb
  have h2 (q : Pattern) (ha : d10887 q = 1) (hb : d146837 q = 1) : d148761 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10887, d148761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10887, d148761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10896 q = 1) (hb : d146837 q = 1) : d148770 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10896, d148770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27830 q ha hb
    | true =>
      simp only [d10896, d148770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27833 q ha hb
  have h4 (q : Pattern) (ha : d10897 q = 1) (hb : d146837 q = 1) : d148771 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10897, d148771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10897, d148771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10898 q = 1) (hb : d146837 q = 1) : d148772 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d10898, d148772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10898, d148772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108867 q = 1) (hb : d146837 q = 1) : d148836 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108867, d148836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27848 q ha hb
    | true =>
      simp only [d108867, d148836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27855 q ha hb
  have h7 (q : Pattern) (ha : d10999 q = 1) (hb : d146837 q = 1) : d148849 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10999, d148849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27834 q ha hb
    | true =>
      simp only [d10999, d148849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27835 q ha hb
  have h8 (q : Pattern) (ha : d108868 q = 1) (hb : d146837 q = 1) : d148850 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108868, d148850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108868, d148850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108869 q = 1) (hb : d146837 q = 1) : d148851 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108869, d148851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108869, d148851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d108870 q = 1) (hb : d146837 q = 1) : d148852 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108870, d148852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108870, d148852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108874 q = 1) (hb : d146837 q = 1) : d148856 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108874, d148856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108874, d148856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27856 q ha hb
  have h12 (q : Pattern) (ha : d11008 q = 1) (hb : d146837 q = 1) : d148858 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11008, d148858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11008, d148858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27836 q ha hb
  have h13 (q : Pattern) (ha : d108875 q = 1) (hb : d146837 q = 1) : d148859 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108875, d148859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108875, d148859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108876 q = 1) (hb : d146837 q = 1) : d148860 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108876, d148860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108876, d148860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d108877 q = 1) (hb : d146837 q = 1) : d148861 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108877, d148861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108877, d148861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d108878 q = 1) (hb : d146837 q = 1) : d148862 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108878, d148862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108878, d148862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108884 q = 1) (hb : d146837 q = 1) : d148901 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108884, d148901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108884, d148901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27863 q ha hb
  have h18 (q : Pattern) (ha : d11083 q = 1) (hb : d146837 q = 1) : d148912 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11083, d148912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11083, d148912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27839 q ha hb
  have h19 (q : Pattern) (ha : d108885 q = 1) (hb : d146837 q = 1) : d148913 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108885, d148913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108885, d148913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d108886 q = 1) (hb : d146837 q = 1) : d148914 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108886, d148914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d108886, d148914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d108887 q = 1) (hb : d146837 q = 1) : d148915 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108887, d148915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d108887, d148915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d108888 q = 1) (hb : d146837 q = 1) : d148916 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108888, d148916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108888, d148916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d108889 q = 1) (hb : d146837 q = 1) : d148917 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108889, d148917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108889, d148917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro27865 (p : Pattern) (ha : d108895 p = 1) (hb : d146837 p = 1) : d148923 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108890 q = 1) (hb : d146837 q = 1) : d148918 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108890, d148918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108890, d148918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27864 q ha hb
  have h2 (q : Pattern) (ha : d108891 q = 1) (hb : d146837 q = 1) : d148919 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108891, d148919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108891, d148919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108892 q = 1) (hb : d146837 q = 1) : d148920 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108892, d148920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108892, d148920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108893 q = 1) (hb : d146837 q = 1) : d148921 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108893, d148921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108893, d148921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108894 q = 1) (hb : d146837 q = 1) : d148922 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108894, d148922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108894, d148922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108895 q = 1) (hb : d146837 q = 1) : d148923 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108895, d148923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108895, d148923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27866 (p : Pattern) (ha : d756 p = 1) (hb : d146836 p = 1) : d148790 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d543 q = 1) (hb : d116750 q = 1) : d21183 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19889 q ha hb
    | true =>
      simp only [d543, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d544 q = 1) (hb : d116750 q = 1) : d21184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d544, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d545 q = 1) (hb : d116750 q = 1) : d21185 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d545, d21185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d545, d21185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d546 q = 1) (hb : d116750 q = 1) : d21186 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d546, d21186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d546, d21186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d319 q = 1) (hb : d116750 q = 1) : d20990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
    | true =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d320 q = 1) (hb : d116750 q = 1) : d20991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d321 q = 1) (hb : d116750 q = 1) : d20992 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d20992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d20992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d322 q = 1) (hb : d116750 q = 1) : d20993 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d20993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d322, d20993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d547 q = 1) (hb : d116750 q = 1) : d21187 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d547, d21187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d547, d21187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d755 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d756 q = 1) (hb : d146836 q = 1) : d148790 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d756, d146836, d148790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d756, d146836, d148790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro27867 (p : Pattern) (ha : d758 p = 1) (hb : d146836 p = 1) : d148642 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d116750 q = 1) : d20990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
    | true =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d320 q = 1) (hb : d116750 q = 1) : d20991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321 q = 1) (hb : d116750 q = 1) : d20992 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d20992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d20992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d116750 q = 1) : d20993 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d20993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322, d20993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d754 q = 1) (hb : d116750 q = 1) : d754 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d755 q = 1) (hb : d116750 q = 1) : d20994 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d755, d20994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d755, d20994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d757 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d758 q = 1) (hb : d146836 q = 1) : d148642 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d758, d146836, d148642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d758, d146836, d148642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro27868 (p : Pattern) (ha : d11105 p = 1) (hb : d146837 p = 1) : d148927 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11096 q = 1) (hb : d146837 q = 1) : d148791 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11096, d146837, d148791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27866 q ha hb
    | true =>
      simp only [d11096, d146837, d148791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11097 q = 1) (hb : d146837 q = 1) : d148792 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11097, d148792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11097, d148792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11098 q = 1) (hb : d146837 q = 1) : d148793 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11098, d148793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11098, d148793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11099 q = 1) (hb : d146837 q = 1) : d148643 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11099, d146837, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27867 q ha hb
    | true =>
      simp only [d11099, d146837, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11100 q = 1) (hb : d146837 q = 1) : d148644 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11100, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11100, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11101 q = 1) (hb : d146837 q = 1) : d148645 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11101, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11101, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11102 q = 1) (hb : d146837 q = 1) : d148794 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11102, d148794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11102, d148794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11103 q = 1) (hb : d146837 q = 1) : d148925 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11103, d148925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11103, d148925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11104 q = 1) (hb : d146837 q = 1) : d148926 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11104, d148926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11104, d148926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11105 q = 1) (hb : d146837 q = 1) : d148927 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11105, d148927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11105, d148927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro27869 (p : Pattern) (ha : d11109 p = 1) (hb : d146837 p = 1) : d148931 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11099 q = 1) (hb : d146837 q = 1) : d148643 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11099, d146837, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27867 q ha hb
    | true =>
      simp only [d11099, d146837, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11100 q = 1) (hb : d146837 q = 1) : d148644 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11100, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11100, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11101 q = 1) (hb : d146837 q = 1) : d148645 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11101, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11101, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11103 q = 1) (hb : d146837 q = 1) : d148925 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11103, d148925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11103, d148925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11108 q = 1) (hb : d146837 q = 1) : d148930 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11108, d148930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11108, d148930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11109 q = 1) (hb : d146837 q = 1) : d148931 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11109, d148931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11109, d148931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro27870 (p : Pattern) (ha : d11115 p = 1) (hb : d146837 p = 1) : d148937 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d146837 q = 1) : d148928 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27868 q ha hb
    | true =>
      simp only [d11106, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d146837 q = 1) : d148929 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d146837 q = 1) : d148932 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27869 q ha hb
    | true =>
      simp only [d11110, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d146837 q = 1) : d148933 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11112 q = 1) (hb : d146837 q = 1) : d148934 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d148934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d148934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11113 q = 1) (hb : d146837 q = 1) : d148935 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11113, d148935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11113, d148935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11114 q = 1) (hb : d146837 q = 1) : d148936 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11114, d148936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11114, d148936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11115 q = 1) (hb : d146837 q = 1) : d148937 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11115, d148937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11115, d148937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27871 (p : Pattern) (ha : d11119 p = 1) (hb : d146837 p = 1) : d148941 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11110 q = 1) (hb : d146837 q = 1) : d148932 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27869 q ha hb
    | true =>
      simp only [d11110, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11111 q = 1) (hb : d146837 q = 1) : d148933 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11116 q = 1) (hb : d146837 q = 1) : d148938 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d148938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11116, d148938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11117 q = 1) (hb : d146837 q = 1) : d148939 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11117, d148939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11117, d148939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11118 q = 1) (hb : d146837 q = 1) : d148940 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11118, d148940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11118, d148940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11119 q = 1) (hb : d146837 q = 1) : d148941 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11119, d148941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11119, d148941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27872 (p : Pattern) (ha : d11125 p = 1) (hb : d146837 p = 1) : d148947 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11120 q = 1) (hb : d146837 q = 1) : d148942 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11120, d148942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27870 q ha hb
    | true =>
      simp only [d11120, d148942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27871 q ha hb
  have h2 (q : Pattern) (ha : d11121 q = 1) (hb : d146837 q = 1) : d148943 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11121, d148943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11121, d148943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11122 q = 1) (hb : d146837 q = 1) : d148944 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11122, d148944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11122, d148944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11123 q = 1) (hb : d146837 q = 1) : d148945 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11123, d148945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11123, d148945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11124 q = 1) (hb : d146837 q = 1) : d148946 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11124, d148946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11124, d148946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11125 q = 1) (hb : d146837 q = 1) : d148947 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11125, d148947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11125, d148947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27873 (p : Pattern) (ha : d11128 p = 1) (hb : d146837 p = 1) : d148950 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d146837 q = 1) : d148928 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27868 q ha hb
    | true =>
      simp only [d11106, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d146837 q = 1) : d148929 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d146837 q = 1) : d148932 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27869 q ha hb
    | true =>
      simp only [d11110, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d146837 q = 1) : d148933 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11112 q = 1) (hb : d146837 q = 1) : d148934 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d148934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d148934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11113 q = 1) (hb : d146837 q = 1) : d148935 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11113, d148935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11113, d148935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11114 q = 1) (hb : d146837 q = 1) : d148936 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11114, d148936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11114, d148936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11128 q = 1) (hb : d146837 q = 1) : d148950 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11128, d148950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11128, d148950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27874 (p : Pattern) (ha : d11129 p = 1) (hb : d146837 p = 1) : d148951 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11110 q = 1) (hb : d146837 q = 1) : d148932 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27869 q ha hb
    | true =>
      simp only [d11110, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11111 q = 1) (hb : d146837 q = 1) : d148933 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11116 q = 1) (hb : d146837 q = 1) : d148938 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d148938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11116, d148938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11117 q = 1) (hb : d146837 q = 1) : d148939 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11117, d148939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11117, d148939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11118 q = 1) (hb : d146837 q = 1) : d148940 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11118, d148940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11118, d148940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11129 q = 1) (hb : d146837 q = 1) : d148951 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11129, d148951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11129, d148951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27875 (p : Pattern) (ha : d11135 p = 1) (hb : d146837 p = 1) : d148957 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11120 q = 1) (hb : d146837 q = 1) : d148942 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11120, d148942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27870 q ha hb
    | true =>
      simp only [d11120, d148942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27871 q ha hb
  have h2 (q : Pattern) (ha : d11121 q = 1) (hb : d146837 q = 1) : d148943 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11121, d148943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11121, d148943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11122 q = 1) (hb : d146837 q = 1) : d148944 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11122, d148944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11122, d148944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11123 q = 1) (hb : d146837 q = 1) : d148945 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11123, d148945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11123, d148945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11124 q = 1) (hb : d146837 q = 1) : d148946 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11124, d148946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11124, d148946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11130 q = 1) (hb : d146837 q = 1) : d148952 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11130, d148952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27873 q ha hb
    | true =>
      simp only [d11130, d148952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27874 q ha hb
  have h7 (q : Pattern) (ha : d11131 q = 1) (hb : d146837 q = 1) : d148953 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11131, d148953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11131, d148953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11132 q = 1) (hb : d146837 q = 1) : d148954 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11132, d148954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11132, d148954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11133 q = 1) (hb : d146837 q = 1) : d148955 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11133, d148955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11133, d148955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11134 q = 1) (hb : d146837 q = 1) : d148956 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11134, d148956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11134, d148956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11135 q = 1) (hb : d146837 q = 1) : d148957 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11135, d148957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11135, d148957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27876 (p : Pattern) (ha : d11243 p = 1) (hb : d146837 p = 1) : d149030 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11120 q = 1) (hb : d146837 q = 1) : d148942 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11120, d148942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27870 q ha hb
    | true =>
      simp only [d11120, d148942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27871 q ha hb
  have h2 (q : Pattern) (ha : d11121 q = 1) (hb : d146837 q = 1) : d148943 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11121, d148943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11121, d148943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11122 q = 1) (hb : d146837 q = 1) : d148944 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11122, d148944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11122, d148944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11123 q = 1) (hb : d146837 q = 1) : d148945 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11123, d148945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11123, d148945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11124 q = 1) (hb : d146837 q = 1) : d148946 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11124, d148946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11124, d148946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11238 q = 1) (hb : d146837 q = 1) : d149025 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11238, d149025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27871 q ha hb
    | true =>
      simp only [d11238, d149025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11239 q = 1) (hb : d146837 q = 1) : d149026 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11239, d149026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11239, d149026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11240 q = 1) (hb : d146837 q = 1) : d149027 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11240, d149027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11240, d149027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11241 q = 1) (hb : d146837 q = 1) : d149028 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11241, d149028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11241, d149028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11242 q = 1) (hb : d146837 q = 1) : d149029 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11242, d149029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11242, d149029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11243 q = 1) (hb : d146837 q = 1) : d149030 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11243, d149030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11243, d149030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27877 (p : Pattern) (ha : d11249 p = 1) (hb : d146837 p = 1) : d149036 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11238 q = 1) (hb : d146837 q = 1) : d149025 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11238, d149025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27871 q ha hb
    | true =>
      simp only [d11238, d149025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11239 q = 1) (hb : d146837 q = 1) : d149026 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11239, d149026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11239, d149026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11240 q = 1) (hb : d146837 q = 1) : d149027 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11240, d149027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11240, d149027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11241 q = 1) (hb : d146837 q = 1) : d149028 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11241, d149028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11241, d149028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11242 q = 1) (hb : d146837 q = 1) : d149029 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11242, d149029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11242, d149029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11244 q = 1) (hb : d146837 q = 1) : d149031 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11244, d149031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27874 q ha hb
    | true =>
      simp only [d11244, d149031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11245 q = 1) (hb : d146837 q = 1) : d149032 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11245, d149032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11245, d149032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11246 q = 1) (hb : d146837 q = 1) : d149033 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11246, d149033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11246, d149033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11247 q = 1) (hb : d146837 q = 1) : d149034 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11247, d149034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11247, d149034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11248 q = 1) (hb : d146837 q = 1) : d149035 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11248, d149035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11248, d149035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11249 q = 1) (hb : d146837 q = 1) : d149036 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11249, d149036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11249, d149036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27878 (p : Pattern) (ha : d11258 p = 1) (hb : d146837 p = 1) : d149045 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11244 q = 1) (hb : d146837 q = 1) : d149031 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11244, d149031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27874 q ha hb
    | true =>
      simp only [d11244, d149031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11245 q = 1) (hb : d146837 q = 1) : d149032 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11245, d149032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11245, d149032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11246 q = 1) (hb : d146837 q = 1) : d149033 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11246, d149033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11246, d149033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11247 q = 1) (hb : d146837 q = 1) : d149034 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11247, d149034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11247, d149034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11248 q = 1) (hb : d146837 q = 1) : d149035 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11248, d149035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11248, d149035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11258 q = 1) (hb : d146837 q = 1) : d149045 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11258, d149045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11258, d149045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27879 (p : Pattern) (ha : d981 p = 1) (hb : d146836 p = 1) : d148700 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d412 q = 1) (hb : d116750 q = 1) : d21071 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d21071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d21071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d116750 q = 1) : d20990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
    | true =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d413 q = 1) (hb : d116750 q = 1) : d21072 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d21072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d413, d21072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320 q = 1) (hb : d116750 q = 1) : d20991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d414 q = 1) (hb : d116750 q = 1) : d21073 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d21073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d414, d21073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d415 q = 1) (hb : d116750 q = 1) : d21074 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d21074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d415, d21074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d974 q = 1) (hb : d116750 q = 1) : d974 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d975 q = 1) (hb : d116750 q = 1) : d21075 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d975, d21075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d975, d21075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d980 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d981 q = 1) (hb : d146836 q = 1) : d148700 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d981, d146836, d148700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d981, d146836, d148700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro27880 (p : Pattern) (ha : d11289 p = 1) (hb : d146837 p = 1) : d149070 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11271 q = 1) (hb : d146837 q = 1) : d148701 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11271, d146837, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27879 q ha hb
    | true =>
      simp only [d11271, d146837, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11272 q = 1) (hb : d146837 q = 1) : d148702 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11272, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11272, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11273 q = 1) (hb : d146837 q = 1) : d148703 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11273, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11273, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11279 q = 1) (hb : d146837 q = 1) : d149060 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11279, d149060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11279, d149060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11288 q = 1) (hb : d146837 q = 1) : d149069 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11288, d149069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11288, d149069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11289 q = 1) (hb : d146837 q = 1) : d149070 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11289, d149070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11289, d149070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro27881 (p : Pattern) (ha : d11345 p = 1) (hb : d146837 p = 1) : d149093 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11290 q = 1) (hb : d146837 q = 1) : d149071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11290, d149071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27880 q ha hb
    | true =>
      simp only [d11290, d149071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11291 q = 1) (hb : d146837 q = 1) : d149072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11291, d149072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11291, d149072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11342 q = 1) (hb : d146837 q = 1) : d149090 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11342, d149090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11342, d149090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11343 q = 1) (hb : d146837 q = 1) : d149091 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11343, d149091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11343, d149091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11344 q = 1) (hb : d146837 q = 1) : d149092 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11344, d149092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11344, d149092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11345 q = 1) (hb : d146837 q = 1) : d149093 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11345, d149093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11345, d149093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27882 (p : Pattern) (ha : d11351 p = 1) (hb : d146837 p = 1) : d149099 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11346 q = 1) (hb : d146837 q = 1) : d149094 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11346, d149094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27881 q ha hb
    | true =>
      simp only [d11346, d149094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11347 q = 1) (hb : d146837 q = 1) : d149095 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11347, d149095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11347, d149095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11348 q = 1) (hb : d146837 q = 1) : d149096 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11348, d149096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11348, d149096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11349 q = 1) (hb : d146837 q = 1) : d149097 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11349, d149097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11349, d149097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11350 q = 1) (hb : d146837 q = 1) : d149098 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11350, d149098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11350, d149098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11351 q = 1) (hb : d146837 q = 1) : d149099 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11351, d149099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11351, d149099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27883 (p : Pattern) (ha : d11140 p = 1) (hb : d146837 p = 1) : d148962 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d146837 q = 1) : d148928 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27868 q ha hb
    | true =>
      simp only [d11106, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d146837 q = 1) : d148929 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d146837 q = 1) : d148932 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27869 q ha hb
    | true =>
      simp only [d11110, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d146837 q = 1) : d148933 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11112 q = 1) (hb : d146837 q = 1) : d148934 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d148934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d148934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11113 q = 1) (hb : d146837 q = 1) : d148935 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11113, d148935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11113, d148935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11139 q = 1) (hb : d146837 q = 1) : d148961 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11139, d148961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11139, d148961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11140 q = 1) (hb : d146837 q = 1) : d148962 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11140, d148962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11140, d148962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27884 (p : Pattern) (ha : d11142 p = 1) (hb : d146837 p = 1) : d148964 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11110 q = 1) (hb : d146837 q = 1) : d148932 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27869 q ha hb
    | true =>
      simp only [d11110, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11111 q = 1) (hb : d146837 q = 1) : d148933 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11116 q = 1) (hb : d146837 q = 1) : d148938 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d148938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11116, d148938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11117 q = 1) (hb : d146837 q = 1) : d148939 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11117, d148939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11117, d148939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11141 q = 1) (hb : d146837 q = 1) : d148963 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11141, d148963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11141, d148963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11142 q = 1) (hb : d146837 q = 1) : d148964 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11142, d148964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11142, d148964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27885 (p : Pattern) (ha : d11149 p = 1) (hb : d146837 p = 1) : d148971 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d146837 q = 1) : d148928 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27868 q ha hb
    | true =>
      simp only [d11106, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d146837 q = 1) : d148929 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d146837 q = 1) : d148932 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27869 q ha hb
    | true =>
      simp only [d11110, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d146837 q = 1) : d148933 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11112 q = 1) (hb : d146837 q = 1) : d148934 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d148934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d148934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11147 q = 1) (hb : d146837 q = 1) : d148969 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11147, d148969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11147, d148969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11148 q = 1) (hb : d146837 q = 1) : d148970 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11148, d148970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11148, d148970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11149 q = 1) (hb : d146837 q = 1) : d148971 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11149, d148971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11149, d148971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27886 (p : Pattern) (ha : d11152 p = 1) (hb : d146837 p = 1) : d148974 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11110 q = 1) (hb : d146837 q = 1) : d148932 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27869 q ha hb
    | true =>
      simp only [d11110, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11111 q = 1) (hb : d146837 q = 1) : d148933 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11116 q = 1) (hb : d146837 q = 1) : d148938 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d148938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11116, d148938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11150 q = 1) (hb : d146837 q = 1) : d148972 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11150, d148972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11150, d148972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11151 q = 1) (hb : d146837 q = 1) : d148973 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11151, d148973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11151, d148973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11152 q = 1) (hb : d146837 q = 1) : d148974 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11152, d148974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11152, d148974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27887 (p : Pattern) (ha : d833 p = 1) (hb : d116750 p = 1) : d21481 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d832 q = 1) : d832 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d541 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d833 q = 1) (hb : d116750 q = 1) : d21481 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d833, d116750, d21481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d833, d116750, d21481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro27888 (p : Pattern) (ha : d839 p = 1) (hb : d146836 p = 1) : d148978 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d834 q = 1) (hb : d116750 q = 1) : d21482 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d834, d21482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27887 q ha hb
    | true =>
      simp only [d834, d21482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d835 q = 1) (hb : d116750 q = 1) : d21483 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d835, d21483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d835, d21483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d836 q = 1) (hb : d116750 q = 1) : d21484 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d836, d21484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d836, d21484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d837 q = 1) (hb : d116750 q = 1) : d21485 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d837, d21485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d837, d21485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d543 q = 1) (hb : d116750 q = 1) : d21183 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19889 q ha hb
    | true =>
      simp only [d543, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d544 q = 1) (hb : d116750 q = 1) : d21184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d544, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d545 q = 1) (hb : d116750 q = 1) : d21185 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d545, d21185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d545, d21185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d546 q = 1) (hb : d116750 q = 1) : d21186 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d546, d21186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d546, d21186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d838 q = 1) (hb : d116750 q = 1) : d21486 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d838, d21486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d838, d21486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d547 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d839 q = 1) (hb : d146836 q = 1) : d148978 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d839, d146836, d148978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d839, d146836, d148978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro27889 (p : Pattern) (ha : d11161 p = 1) (hb : d146837 p = 1) : d148984 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11156 q = 1) (hb : d146837 q = 1) : d148979 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11156, d146837, d148979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27888 q ha hb
    | true =>
      simp only [d11156, d146837, d148979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11157 q = 1) (hb : d146837 q = 1) : d148980 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11157, d148980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11157, d148980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11158 q = 1) (hb : d146837 q = 1) : d148981 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11158, d148981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11158, d148981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11096 q = 1) (hb : d146837 q = 1) : d148791 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11096, d146837, d148791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27866 q ha hb
    | true =>
      simp only [d11096, d146837, d148791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11097 q = 1) (hb : d146837 q = 1) : d148792 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11097, d148792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11097, d148792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11098 q = 1) (hb : d146837 q = 1) : d148793 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11098, d148793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11098, d148793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11159 q = 1) (hb : d146837 q = 1) : d148982 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11159, d148982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11159, d148982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11099 q = 1) (hb : d146837 q = 1) : d148643 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11099, d146837, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27867 q ha hb
    | true =>
      simp only [d11099, d146837, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d11100 q = 1) (hb : d146837 q = 1) : d148644 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11100, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11100, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11101 q = 1) (hb : d146837 q = 1) : d148645 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11101, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11101, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11102 q = 1) (hb : d146837 q = 1) : d148794 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11102, d148794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11102, d148794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11160 q = 1) (hb : d146837 q = 1) : d148983 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11160, d148983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11160, d148983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11161 q = 1) (hb : d146837 q = 1) : d148984 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11161, d148984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11161, d148984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro27890 (p : Pattern) (ha : d11167 p = 1) (hb : d146837 p = 1) : d148990 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11162 q = 1) (hb : d146837 q = 1) : d148985 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11162, d148985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27889 q ha hb
    | true =>
      simp only [d11162, d148985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11163 q = 1) (hb : d146837 q = 1) : d148986 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11163, d148986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11163, d148986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11106 q = 1) (hb : d146837 q = 1) : d148928 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27868 q ha hb
    | true =>
      simp only [d11106, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11107 q = 1) (hb : d146837 q = 1) : d148929 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11164 q = 1) (hb : d146837 q = 1) : d148987 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11164, d148987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11164, d148987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11165 q = 1) (hb : d146837 q = 1) : d148988 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11165, d148988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11165, d148988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11166 q = 1) (hb : d146837 q = 1) : d148989 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11166, d148989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11166, d148989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11167 q = 1) (hb : d146837 q = 1) : d148990 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11167, d148990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11167, d148990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27891 (p : Pattern) (ha : d5456 p = 1) (hb : d146836 p = 1) : d148642 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d116750 q = 1) : d20990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
    | true =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d320 q = 1) (hb : d116750 q = 1) : d20991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321 q = 1) (hb : d116750 q = 1) : d20992 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d20992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d20992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d116750 q = 1) : d20993 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d20993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322, d20993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d754 q = 1) (hb : d116750 q = 1) : d754 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d755 q = 1) (hb : d116750 q = 1) : d20994 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d755, d20994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d755, d20994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d5455 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d5456 q = 1) (hb : d146836 q = 1) : d148642 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5456, d146836, d148642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5456, d146836, d148642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro27892 (p : Pattern) (ha : d11200 p = 1) (hb : d146837 p = 1) : d148927 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11096 q = 1) (hb : d146837 q = 1) : d148791 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11096, d146837, d148791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27866 q ha hb
    | true =>
      simp only [d11096, d146837, d148791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11097 q = 1) (hb : d146837 q = 1) : d148792 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11097, d148792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11097, d148792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11098 q = 1) (hb : d146837 q = 1) : d148793 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11098, d148793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11098, d148793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11099 q = 1) (hb : d146837 q = 1) : d148643 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11099, d146837, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27867 q ha hb
    | true =>
      simp only [d11099, d146837, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11100 q = 1) (hb : d146837 q = 1) : d148644 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11100, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11100, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11101 q = 1) (hb : d146837 q = 1) : d148645 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11101, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11101, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11102 q = 1) (hb : d146837 q = 1) : d148794 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11102, d148794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11102, d148794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11195 q = 1) (hb : d146837 q = 1) : d148643 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11195, d146837, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27891 q ha hb
    | true =>
      simp only [d11195, d146837, d148643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d11196 q = 1) (hb : d146837 q = 1) : d148644 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11196, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11196, d148644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11197 q = 1) (hb : d146837 q = 1) : d148645 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11197, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11197, d148645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11198 q = 1) (hb : d146837 q = 1) : d148925 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11198, d148925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d11198, d148925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d11199 q = 1) (hb : d146837 q = 1) : d148926 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11199, d148926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11199, d148926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11200 q = 1) (hb : d146837 q = 1) : d148927 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11200, d148927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11200, d148927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro27893 (p : Pattern) (ha : d11206 p = 1) (hb : d146837 p = 1) : d148996 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11201 q = 1) (hb : d146837 q = 1) : d148928 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11201, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27892 q ha hb
    | true =>
      simp only [d11201, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11202 q = 1) (hb : d146837 q = 1) : d148929 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11202, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11202, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11203 q = 1) (hb : d146837 q = 1) : d148993 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11203, d148993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11203, d148993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11204 q = 1) (hb : d146837 q = 1) : d148994 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11204, d148994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11204, d148994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11205 q = 1) (hb : d146837 q = 1) : d148995 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11205, d148995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11205, d148995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11206 q = 1) (hb : d146837 q = 1) : d148996 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11206, d148996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11206, d148996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27894 (p : Pattern) (ha : d108901 p = 1) (hb : d146837 p = 1) : d149002 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11143 q = 1) (hb : d146837 q = 1) : d148965 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11143, d148965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27883 q ha hb
    | true =>
      simp only [d11143, d148965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27884 q ha hb
  have h2 (q : Pattern) (ha : d11144 q = 1) (hb : d146837 q = 1) : d148966 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11144, d148966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11144, d148966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11145 q = 1) (hb : d146837 q = 1) : d148967 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11145, d148967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11145, d148967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11146 q = 1) (hb : d146837 q = 1) : d148968 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11146, d148968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11146, d148968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11153 q = 1) (hb : d146837 q = 1) : d148975 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11153, d148975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27885 q ha hb
    | true =>
      simp only [d11153, d148975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27886 q ha hb
  have h6 (q : Pattern) (ha : d11154 q = 1) (hb : d146837 q = 1) : d148976 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11154, d148976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11154, d148976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11155 q = 1) (hb : d146837 q = 1) : d148977 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11155, d148977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11155, d148977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11168 q = 1) (hb : d146837 q = 1) : d148991 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11168, d148991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27890 q ha hb
    | true =>
      simp only [d11168, d148991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27870 q ha hb
  have h9 (q : Pattern) (ha : d108897 q = 1) (hb : d146837 q = 1) : d148992 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108897, d148992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108897, d148992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11207 q = 1) (hb : d146837 q = 1) : d148997 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11207, d148997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27893 q ha hb
    | true =>
      simp only [d11207, d148997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11208 q = 1) (hb : d146837 q = 1) : d148998 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11208, d148998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11208, d148998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d108898 q = 1) (hb : d146837 q = 1) : d148999 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108898, d148999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108898, d148999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108899 q = 1) (hb : d146837 q = 1) : d149000 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108899, d149000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108899, d149000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108900 q = 1) (hb : d146837 q = 1) : d149001 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108900, d149001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108900, d149001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108901 q = 1) (hb : d146837 q = 1) : d149002 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108901, d149002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108901, d149002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro27895 (p : Pattern) (ha : d11213 p = 1) (hb : d146837 p = 1) : d149003 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d146837 q = 1) : d148928 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27868 q ha hb
    | true =>
      simp only [d11106, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d146837 q = 1) : d148929 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d146837 q = 1) : d148932 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27869 q ha hb
    | true =>
      simp only [d11110, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d146837 q = 1) : d148933 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11112 q = 1) (hb : d146837 q = 1) : d148934 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d148934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d148934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11113 q = 1) (hb : d146837 q = 1) : d148935 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11113, d148935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11113, d148935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11139 q = 1) (hb : d146837 q = 1) : d148961 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11139, d148961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11139, d148961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11213 q = 1) (hb : d146837 q = 1) : d149003 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11213, d149003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11213, d149003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27896 (p : Pattern) (ha : d11214 p = 1) (hb : d146837 p = 1) : d149004 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11110 q = 1) (hb : d146837 q = 1) : d148932 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27869 q ha hb
    | true =>
      simp only [d11110, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11111 q = 1) (hb : d146837 q = 1) : d148933 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11116 q = 1) (hb : d146837 q = 1) : d148938 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d148938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11116, d148938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11117 q = 1) (hb : d146837 q = 1) : d148939 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11117, d148939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11117, d148939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11141 q = 1) (hb : d146837 q = 1) : d148963 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11141, d148963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11141, d148963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11214 q = 1) (hb : d146837 q = 1) : d149004 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11214, d149004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11214, d149004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27897 (p : Pattern) (ha : d11219 p = 1) (hb : d146837 p = 1) : d149009 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d146837 q = 1) : d148928 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27868 q ha hb
    | true =>
      simp only [d11106, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d146837 q = 1) : d148929 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d146837 q = 1) : d148932 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27869 q ha hb
    | true =>
      simp only [d11110, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d146837 q = 1) : d148933 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11112 q = 1) (hb : d146837 q = 1) : d148934 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d148934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d148934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11147 q = 1) (hb : d146837 q = 1) : d148969 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11147, d148969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11147, d148969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11148 q = 1) (hb : d146837 q = 1) : d148970 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11148, d148970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11148, d148970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11219 q = 1) (hb : d146837 q = 1) : d149009 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11219, d149009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11219, d149009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27898 (p : Pattern) (ha : d11220 p = 1) (hb : d146837 p = 1) : d149010 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11110 q = 1) (hb : d146837 q = 1) : d148932 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27869 q ha hb
    | true =>
      simp only [d11110, d148932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11111 q = 1) (hb : d146837 q = 1) : d148933 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d148933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11116 q = 1) (hb : d146837 q = 1) : d148938 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d148938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11116, d148938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11150 q = 1) (hb : d146837 q = 1) : d148972 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11150, d148972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11150, d148972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11151 q = 1) (hb : d146837 q = 1) : d148973 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11151, d148973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11151, d148973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11220 q = 1) (hb : d146837 q = 1) : d149010 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11220, d149010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11220, d149010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27899 (p : Pattern) (ha : d11224 p = 1) (hb : d146837 p = 1) : d149014 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11162 q = 1) (hb : d146837 q = 1) : d148985 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11162, d148985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27889 q ha hb
    | true =>
      simp only [d11162, d148985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11163 q = 1) (hb : d146837 q = 1) : d148986 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11163, d148986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11163, d148986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11106 q = 1) (hb : d146837 q = 1) : d148928 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27868 q ha hb
    | true =>
      simp only [d11106, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11107 q = 1) (hb : d146837 q = 1) : d148929 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11164 q = 1) (hb : d146837 q = 1) : d148987 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11164, d148987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11164, d148987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11165 q = 1) (hb : d146837 q = 1) : d148988 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11165, d148988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11165, d148988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11166 q = 1) (hb : d146837 q = 1) : d148989 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11166, d148989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11166, d148989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11224 q = 1) (hb : d146837 q = 1) : d149014 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11224, d149014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11224, d149014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27900 (p : Pattern) (ha : d11230 p = 1) (hb : d146837 p = 1) : d149017 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11201 q = 1) (hb : d146837 q = 1) : d148928 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11201, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27892 q ha hb
    | true =>
      simp only [d11201, d148928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11202 q = 1) (hb : d146837 q = 1) : d148929 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11202, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11202, d148929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11203 q = 1) (hb : d146837 q = 1) : d148993 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11203, d148993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11203, d148993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11204 q = 1) (hb : d146837 q = 1) : d148994 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11204, d148994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11204, d148994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11205 q = 1) (hb : d146837 q = 1) : d148995 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11205, d148995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11205, d148995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11230 q = 1) (hb : d146837 q = 1) : d149017 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11230, d149017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11230, d149017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27901 (p : Pattern) (ha : d108906 p = 1) (hb : d146837 p = 1) : d149023 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11143 q = 1) (hb : d146837 q = 1) : d148965 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11143, d148965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27883 q ha hb
    | true =>
      simp only [d11143, d148965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27884 q ha hb
  have h2 (q : Pattern) (ha : d11144 q = 1) (hb : d146837 q = 1) : d148966 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11144, d148966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11144, d148966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11145 q = 1) (hb : d146837 q = 1) : d148967 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11145, d148967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11145, d148967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11146 q = 1) (hb : d146837 q = 1) : d148968 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11146, d148968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11146, d148968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11153 q = 1) (hb : d146837 q = 1) : d148975 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11153, d148975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27885 q ha hb
    | true =>
      simp only [d11153, d148975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27886 q ha hb
  have h6 (q : Pattern) (ha : d11154 q = 1) (hb : d146837 q = 1) : d148976 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11154, d148976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11154, d148976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11155 q = 1) (hb : d146837 q = 1) : d148977 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11155, d148977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11155, d148977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11168 q = 1) (hb : d146837 q = 1) : d148991 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11168, d148991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27890 q ha hb
    | true =>
      simp only [d11168, d148991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27870 q ha hb
  have h9 (q : Pattern) (ha : d108897 q = 1) (hb : d146837 q = 1) : d148992 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108897, d148992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108897, d148992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11207 q = 1) (hb : d146837 q = 1) : d148997 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11207, d148997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27893 q ha hb
    | true =>
      simp only [d11207, d148997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11208 q = 1) (hb : d146837 q = 1) : d148998 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11208, d148998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11208, d148998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d108898 q = 1) (hb : d146837 q = 1) : d148999 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108898, d148999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108898, d148999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108899 q = 1) (hb : d146837 q = 1) : d149000 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108899, d149000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108899, d149000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108900 q = 1) (hb : d146837 q = 1) : d149001 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108900, d149001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108900, d149001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d11215 q = 1) (hb : d146837 q = 1) : d149005 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11215, d149005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27895 q ha hb
    | true =>
      simp only [d11215, d149005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27896 q ha hb
  have h16 (q : Pattern) (ha : d11216 q = 1) (hb : d146837 q = 1) : d149006 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11216, d149006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11216, d149006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d11217 q = 1) (hb : d146837 q = 1) : d149007 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11217, d149007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d11217, d149007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d11218 q = 1) (hb : d146837 q = 1) : d149008 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11218, d149008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11218, d149008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d11221 q = 1) (hb : d146837 q = 1) : d149011 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11221, d149011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27897 q ha hb
    | true =>
      simp only [d11221, d149011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27898 q ha hb
  have h20 (q : Pattern) (ha : d11222 q = 1) (hb : d146837 q = 1) : d149012 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11222, d149012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11222, d149012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d11223 q = 1) (hb : d146837 q = 1) : d149013 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11223, d149013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d11223, d149013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d11225 q = 1) (hb : d146837 q = 1) : d149015 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11225, d149015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27899 q ha hb
    | true =>
      simp only [d11225, d149015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27873 q ha hb
  have h23 (q : Pattern) (ha : d108902 q = 1) (hb : d146837 q = 1) : d149016 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108902, d149016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d108902, d149016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d11231 q = 1) (hb : d146837 q = 1) : d149018 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11231, d149018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27900 q ha hb
    | true =>
      simp only [d11231, d149018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d11232 q = 1) (hb : d146837 q = 1) : d149019 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11232, d149019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d11232, d149019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d108903 q = 1) (hb : d146837 q = 1) : d149020 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108903, d149020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d108903, d149020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d108904 q = 1) (hb : d146837 q = 1) : d149021 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108904, d149021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108904, d149021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d108905 q = 1) (hb : d146837 q = 1) : d149022 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108905, d149022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d108905, d149022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d108906 q = 1) (hb : d146837 q = 1) : d149023 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108906, d149023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108906, d149023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro27902 (p : Pattern) (ha : d108913 p = 1) (hb : d146837 p = 1) : d149043 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11225 q = 1) (hb : d146837 q = 1) : d149015 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11225, d149015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27899 q ha hb
    | true =>
      simp only [d11225, d149015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27873 q ha hb
  have h2 (q : Pattern) (ha : d108902 q = 1) (hb : d146837 q = 1) : d149016 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108902, d149016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108902, d149016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11231 q = 1) (hb : d146837 q = 1) : d149018 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11231, d149018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27900 q ha hb
    | true =>
      simp only [d11231, d149018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11232 q = 1) (hb : d146837 q = 1) : d149019 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11232, d149019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11232, d149019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108903 q = 1) (hb : d146837 q = 1) : d149020 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108903, d149020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108903, d149020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108911 q = 1) (hb : d146837 q = 1) : d149041 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108911, d149041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108911, d149041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108912 q = 1) (hb : d146837 q = 1) : d149042 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108912, d149042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108912, d149042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108913 q = 1) (hb : d146837 q = 1) : d149043 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108913, d149043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108913, d149043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27903 (p : Pattern) (ha : d970 p = 1) (hb : d146836 p = 1) : d149051 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d965 q = 1) (hb : d116750 q = 1) : d21612 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d965, d21612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d965, d21612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27887 q ha hb
  have h2 (q : Pattern) (ha : d834 q = 1) (hb : d116750 q = 1) : d21482 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d834, d21482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27887 q ha hb
    | true =>
      simp only [d834, d21482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d966 q = 1) (hb : d116750 q = 1) : d21613 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d966, d21613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d966, d21613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d835 q = 1) (hb : d116750 q = 1) : d21483 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d835, d21483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d835, d21483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d967 q = 1) (hb : d116750 q = 1) : d21614 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d967, d21614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d967, d21614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d968 q = 1) (hb : d116750 q = 1) : d21615 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d968, d21615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d968, d21615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d659 q = 1) (hb : d116750 q = 1) : d21309 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d659, d21309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d659, d21309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19889 q ha hb
  have h8 (q : Pattern) (ha : d543 q = 1) (hb : d116750 q = 1) : d21183 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19889 q ha hb
    | true =>
      simp only [d543, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d660 q = 1) (hb : d116750 q = 1) : d21310 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, d21310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d660, d21310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d544 q = 1) (hb : d116750 q = 1) : d21184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d544, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d661 q = 1) (hb : d116750 q = 1) : d21311 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d661, d21311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d661, d21311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d662 q = 1) (hb : d116750 q = 1) : d21312 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d662, d21312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d662, d21312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d969 q = 1) (hb : d116750 q = 1) : d21616 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d969, d21616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d969, d21616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d663 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d970 q = 1) (hb : d146836 q = 1) : d149051 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d970, d146836, d149051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d970, d146836, d149051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro27904 (p : Pattern) (ha : d976 p = 1) (hb : d146836 p = 1) : d148863 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d659 q = 1) (hb : d116750 q = 1) : d21309 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d659, d21309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d659, d21309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19889 q ha hb
  have h2 (q : Pattern) (ha : d543 q = 1) (hb : d116750 q = 1) : d21183 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19889 q ha hb
    | true =>
      simp only [d543, d21183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d660 q = 1) (hb : d116750 q = 1) : d21310 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, d21310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d660, d21310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d544 q = 1) (hb : d116750 q = 1) : d21184 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d544, d21184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d661 q = 1) (hb : d116750 q = 1) : d21311 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d661, d21311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d661, d21311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d662 q = 1) (hb : d116750 q = 1) : d21312 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d662, d21312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d662, d21312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d412 q = 1) (hb : d116750 q = 1) : d21071 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d21071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d21071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
  have h8 (q : Pattern) (ha : d319 q = 1) (hb : d116750 q = 1) : d20990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
    | true =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d413 q = 1) (hb : d116750 q = 1) : d21072 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d21072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d413, d21072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d320 q = 1) (hb : d116750 q = 1) : d20991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d414 q = 1) (hb : d116750 q = 1) : d21073 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d21073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d414, d21073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d415 q = 1) (hb : d116750 q = 1) : d21074 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d21074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d415, d21074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d663 q = 1) (hb : d116750 q = 1) : d21313 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d663, d21313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d663, d21313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d975 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d976 q = 1) (hb : d146836 q = 1) : d148863 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d976, d146836, d148863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d976, d146836, d148863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro27905 (p : Pattern) (ha : d11276 p = 1) (hb : d146837 p = 1) : d149057 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11264 q = 1) (hb : d146837 q = 1) : d149052 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11264, d146837, d149052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27903 q ha hb
    | true =>
      simp only [d11264, d146837, d149052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11265 q = 1) (hb : d146837 q = 1) : d149053 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11265, d149053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11265, d149053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11266 q = 1) (hb : d146837 q = 1) : d149054 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11266, d149054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11266, d149054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11267 q = 1) (hb : d146837 q = 1) : d148864 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11267, d146837, d148864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27904 q ha hb
    | true =>
      simp only [d11267, d146837, d148864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11268 q = 1) (hb : d146837 q = 1) : d148865 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11268, d148865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11268, d148865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11269 q = 1) (hb : d146837 q = 1) : d148866 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11269, d148866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11269, d148866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11270 q = 1) (hb : d146837 q = 1) : d149055 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11270, d149055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11270, d149055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11271 q = 1) (hb : d146837 q = 1) : d148701 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11271, d146837, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27879 q ha hb
    | true =>
      simp only [d11271, d146837, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d11272 q = 1) (hb : d146837 q = 1) : d148702 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11272, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11272, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11273 q = 1) (hb : d146837 q = 1) : d148703 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11273, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11273, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11274 q = 1) (hb : d146837 q = 1) : d148867 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11274, d148867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11274, d148867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11275 q = 1) (hb : d146837 q = 1) : d149056 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11275, d149056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11275, d149056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11276 q = 1) (hb : d146837 q = 1) : d149057 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11276, d149057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11276, d149057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro27906 (p : Pattern) (ha : d11281 p = 1) (hb : d146837 p = 1) : d149062 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11267 q = 1) (hb : d146837 q = 1) : d148864 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11267, d146837, d148864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27904 q ha hb
    | true =>
      simp only [d11267, d146837, d148864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11268 q = 1) (hb : d146837 q = 1) : d148865 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11268, d148865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11268, d148865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11269 q = 1) (hb : d146837 q = 1) : d148866 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11269, d148866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11269, d148866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11271 q = 1) (hb : d146837 q = 1) : d148701 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11271, d146837, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27879 q ha hb
    | true =>
      simp only [d11271, d146837, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11272 q = 1) (hb : d146837 q = 1) : d148702 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11272, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11272, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11273 q = 1) (hb : d146837 q = 1) : d148703 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11273, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11273, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11274 q = 1) (hb : d146837 q = 1) : d148867 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11274, d148867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11274, d148867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11279 q = 1) (hb : d146837 q = 1) : d149060 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11279, d149060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11279, d149060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11280 q = 1) (hb : d146837 q = 1) : d149061 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11280, d149061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11280, d149061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11281 q = 1) (hb : d146837 q = 1) : d149062 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11281, d149062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11281, d149062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro27907 (p : Pattern) (ha : d11287 p = 1) (hb : d146837 p = 1) : d149068 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11277 q = 1) (hb : d146837 q = 1) : d149058 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11277, d149058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27905 q ha hb
    | true =>
      simp only [d11277, d149058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11278 q = 1) (hb : d146837 q = 1) : d149059 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11278, d149059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11278, d149059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11282 q = 1) (hb : d146837 q = 1) : d149063 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11282, d149063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27906 q ha hb
    | true =>
      simp only [d11282, d149063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11283 q = 1) (hb : d146837 q = 1) : d149064 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11283, d149064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11283, d149064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11284 q = 1) (hb : d146837 q = 1) : d149065 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11284, d149065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11284, d149065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11285 q = 1) (hb : d146837 q = 1) : d149066 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11285, d149066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11285, d149066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11286 q = 1) (hb : d146837 q = 1) : d149067 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11286, d149067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11286, d149067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11287 q = 1) (hb : d146837 q = 1) : d149068 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11287, d149068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11287, d149068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27908 (p : Pattern) (ha : d11295 p = 1) (hb : d146837 p = 1) : d149076 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11282 q = 1) (hb : d146837 q = 1) : d149063 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11282, d149063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27906 q ha hb
    | true =>
      simp only [d11282, d149063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11283 q = 1) (hb : d146837 q = 1) : d149064 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11283, d149064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11283, d149064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11290 q = 1) (hb : d146837 q = 1) : d149071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11290, d149071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27880 q ha hb
    | true =>
      simp only [d11290, d149071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11291 q = 1) (hb : d146837 q = 1) : d149072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11291, d149072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11291, d149072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11292 q = 1) (hb : d146837 q = 1) : d149073 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11292, d149073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11292, d149073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11293 q = 1) (hb : d146837 q = 1) : d149074 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11293, d149074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11293, d149074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11294 q = 1) (hb : d146837 q = 1) : d149075 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11294, d149075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11294, d149075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11295 q = 1) (hb : d146837 q = 1) : d149076 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11295, d149076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11295, d149076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27909 (p : Pattern) (ha : d5500 p = 1) (hb : d146836 p = 1) : d148700 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d412 q = 1) (hb : d116750 q = 1) : d21071 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d21071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d21071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d116750 q = 1) : d20990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19838 q ha hb
    | true =>
      simp only [d319, d20990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d413 q = 1) (hb : d116750 q = 1) : d21072 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d21072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d413, d21072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320 q = 1) (hb : d116750 q = 1) : d20991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d20991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d414 q = 1) (hb : d116750 q = 1) : d21073 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d21073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d414, d21073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d415 q = 1) (hb : d116750 q = 1) : d21074 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d21074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d415, d21074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d974 q = 1) (hb : d116750 q = 1) : d974 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d975 q = 1) (hb : d116750 q = 1) : d21075 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d975, d21075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d975, d21075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d5499 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d5500 q = 1) (hb : d146836 q = 1) : d148700 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5500, d146836, d148700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5500, d146836, d148700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro27910 (p : Pattern) (ha : d11328 p = 1) (hb : d146837 p = 1) : d149062 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11267 q = 1) (hb : d146837 q = 1) : d148864 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11267, d146837, d148864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27904 q ha hb
    | true =>
      simp only [d11267, d146837, d148864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11268 q = 1) (hb : d146837 q = 1) : d148865 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11268, d148865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11268, d148865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11269 q = 1) (hb : d146837 q = 1) : d148866 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11269, d148866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11269, d148866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11271 q = 1) (hb : d146837 q = 1) : d148701 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11271, d146837, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27879 q ha hb
    | true =>
      simp only [d11271, d146837, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11272 q = 1) (hb : d146837 q = 1) : d148702 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11272, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11272, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11273 q = 1) (hb : d146837 q = 1) : d148703 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11273, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11273, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11274 q = 1) (hb : d146837 q = 1) : d148867 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11274, d148867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11274, d148867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11323 q = 1) (hb : d146837 q = 1) : d148701 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11323, d146837, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27909 q ha hb
    | true =>
      simp only [d11323, d146837, d148701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d11324 q = 1) (hb : d146837 q = 1) : d148702 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11324, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11324, d148702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11325 q = 1) (hb : d146837 q = 1) : d148703 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11325, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11325, d148703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11326 q = 1) (hb : d146837 q = 1) : d149060 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11326, d149060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d11326, d149060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d11327 q = 1) (hb : d146837 q = 1) : d149061 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11327, d149061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11327, d149061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11328 q = 1) (hb : d146837 q = 1) : d149062 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11328, d149062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11328, d149062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro27911 (p : Pattern) (ha : d11334 p = 1) (hb : d146837 p = 1) : d149082 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11329 q = 1) (hb : d146837 q = 1) : d149063 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11329, d149063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27910 q ha hb
    | true =>
      simp only [d11329, d149063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11330 q = 1) (hb : d146837 q = 1) : d149064 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11330, d149064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11330, d149064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11331 q = 1) (hb : d146837 q = 1) : d149079 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11331, d149079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11331, d149079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11332 q = 1) (hb : d146837 q = 1) : d149080 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11332, d149080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11332, d149080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11333 q = 1) (hb : d146837 q = 1) : d149081 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11333, d149081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11333, d149081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11334 q = 1) (hb : d146837 q = 1) : d149082 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11334, d149082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11334, d149082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27912 (p : Pattern) (ha : d108923 p = 1) (hb : d146837 p = 1) : d149088 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11296 q = 1) (hb : d146837 q = 1) : d149077 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11296, d149077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27907 q ha hb
    | true =>
      simp only [d11296, d149077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27908 q ha hb
  have h2 (q : Pattern) (ha : d108919 q = 1) (hb : d146837 q = 1) : d149078 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108919, d149078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108919, d149078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11335 q = 1) (hb : d146837 q = 1) : d149083 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11335, d149083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27911 q ha hb
    | true =>
      simp only [d11335, d149083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11336 q = 1) (hb : d146837 q = 1) : d149084 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11336, d149084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11336, d149084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108920 q = 1) (hb : d146837 q = 1) : d149085 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108920, d149085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108920, d149085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108921 q = 1) (hb : d146837 q = 1) : d149086 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108921, d149086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108921, d149086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108922 q = 1) (hb : d146837 q = 1) : d149087 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108922, d149087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108922, d149087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108923 q = 1) (hb : d146837 q = 1) : d149088 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108923, d149088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108923, d149088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27913 (p : Pattern) (ha : d108929 p = 1) (hb : d146837 p = 1) : d149105 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11126 q = 1) (hb : d146837 q = 1) : d148948 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11126, d148948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11126, d148948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27872 q ha hb
  have h2 (q : Pattern) (ha : d11127 q = 1) (hb : d146837 q = 1) : d148949 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11127, d148949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11127, d148949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11136 q = 1) (hb : d146837 q = 1) : d148958 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11136, d148958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27872 q ha hb
    | true =>
      simp only [d11136, d148958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27875 q ha hb
  have h4 (q : Pattern) (ha : d11137 q = 1) (hb : d146837 q = 1) : d148959 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11137, d148959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11137, d148959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11138 q = 1) (hb : d146837 q = 1) : d148960 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11138, d148960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11138, d148960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108907 q = 1) (hb : d146837 q = 1) : d149024 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108907, d149024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27894 q ha hb
    | true =>
      simp only [d108907, d149024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27901 q ha hb
  have h7 (q : Pattern) (ha : d11250 q = 1) (hb : d146837 q = 1) : d149037 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11250, d149037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27876 q ha hb
    | true =>
      simp only [d11250, d149037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27877 q ha hb
  have h8 (q : Pattern) (ha : d108908 q = 1) (hb : d146837 q = 1) : d149038 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108908, d149038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108908, d149038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108909 q = 1) (hb : d146837 q = 1) : d149039 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108909, d149039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108909, d149039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d108910 q = 1) (hb : d146837 q = 1) : d149040 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108910, d149040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108910, d149040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108914 q = 1) (hb : d146837 q = 1) : d149044 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108914, d149044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108914, d149044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27902 q ha hb
  have h12 (q : Pattern) (ha : d11259 q = 1) (hb : d146837 q = 1) : d149046 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11259, d149046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11259, d149046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27878 q ha hb
  have h13 (q : Pattern) (ha : d108915 q = 1) (hb : d146837 q = 1) : d149047 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108915, d149047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108915, d149047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108916 q = 1) (hb : d146837 q = 1) : d149048 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108916, d149048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108916, d149048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d108917 q = 1) (hb : d146837 q = 1) : d149049 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108917, d149049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108917, d149049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d108918 q = 1) (hb : d146837 q = 1) : d149050 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108918, d149050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108918, d149050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108924 q = 1) (hb : d146837 q = 1) : d149089 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108924, d149089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108924, d149089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27912 q ha hb
  have h18 (q : Pattern) (ha : d11352 q = 1) (hb : d146837 q = 1) : d149100 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11352, d149100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11352, d149100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27882 q ha hb
  have h19 (q : Pattern) (ha : d108925 q = 1) (hb : d146837 q = 1) : d149101 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108925, d149101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108925, d149101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d108926 q = 1) (hb : d146837 q = 1) : d149102 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108926, d149102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d108926, d149102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d108927 q = 1) (hb : d146837 q = 1) : d149103 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108927, d149103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d108927, d149103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d108928 q = 1) (hb : d146837 q = 1) : d149104 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108928, d149104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108928, d149104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d108929 q = 1) (hb : d146837 q = 1) : d149105 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108929, d149105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108929, d149105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro27914 (p : Pattern) (ha : d108935 p = 1) (hb : d146837 p = 1) : d149111 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108930 q = 1) (hb : d146837 q = 1) : d149106 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108930, d149106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108930, d149106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27913 q ha hb
  have h2 (q : Pattern) (ha : d108931 q = 1) (hb : d146837 q = 1) : d149107 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108931, d149107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108931, d149107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108932 q = 1) (hb : d146837 q = 1) : d149108 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108932, d149108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108932, d149108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108933 q = 1) (hb : d146837 q = 1) : d149109 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108933, d149109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108933, d149109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108934 q = 1) (hb : d146837 q = 1) : d149110 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108934, d149110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108934, d149110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108935 q = 1) (hb : d146837 q = 1) : d149111 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108935, d149111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108935, d149111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27915 (p : Pattern) (ha : d1126 p = 1) (hb : d146836 p = 1) : d149114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1100 q = 1) (hb : d116750 q = 1) : d21737 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d21737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19945 q ha hb
    | true =>
      simp only [d1100, d21737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1101 q = 1) (hb : d116750 q = 1) : d21738 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d21738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1101, d21738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1102 q = 1) (hb : d116750 q = 1) : d21739 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1102, d21739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1102, d21739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1103 q = 1) (hb : d116750 q = 1) : d21740 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1103, d21740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1103, d21740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1110 q = 1) (hb : d116750 q = 1) : d21742 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19929 q ha hb
    | true =>
      simp only [d1110, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1111 q = 1) (hb : d116750 q = 1) : d21743 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1111, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1112 q = 1) (hb : d116750 q = 1) : d21744 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1112, d21744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1112, d21744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1113 q = 1) (hb : d116750 q = 1) : d21745 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1113, d21745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1113, d21745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1114 q = 1) (hb : d116750 q = 1) : d21746 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1114, d21746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1114, d21746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d1125 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d1126 q = 1) (hb : d146836 q = 1) : d149114 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1126, d146836, d149114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1126, d146836, d149114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro27916 (p : Pattern) (ha : d1128 p = 1) (hb : d146836 p = 1) : d149118 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1110 q = 1) (hb : d116750 q = 1) : d21742 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19929 q ha hb
    | true =>
      simp only [d1110, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1111 q = 1) (hb : d116750 q = 1) : d21743 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1111, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1112 q = 1) (hb : d116750 q = 1) : d21744 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1112, d21744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1112, d21744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1113 q = 1) (hb : d116750 q = 1) : d21745 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1113, d21745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1113, d21745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1121 q = 1) (hb : d116750 q = 1) : d21755 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19916 q ha hb
    | true =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1122 q = 1) (hb : d116750 q = 1) : d21756 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1123 q = 1) (hb : d116750 q = 1) : d21757 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d21757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1123, d21757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1124 q = 1) (hb : d116750 q = 1) : d21758 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, d21758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1124, d21758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1125 q = 1) (hb : d116750 q = 1) : d21759 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1125, d21759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1125, d21759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d1127 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d1128 q = 1) (hb : d146836 q = 1) : d149118 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1128, d146836, d149118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1128, d146836, d149118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro27917 (p : Pattern) (ha : d11375 p = 1) (hb : d146837 p = 1) : d149125 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11366 q = 1) (hb : d146837 q = 1) : d149115 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11366, d146837, d149115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27915 q ha hb
    | true =>
      simp only [d11366, d146837, d149115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11367 q = 1) (hb : d146837 q = 1) : d149116 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11367, d149116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11367, d149116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11368 q = 1) (hb : d146837 q = 1) : d149117 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11368, d149117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11368, d149117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11369 q = 1) (hb : d146837 q = 1) : d149119 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11369, d146837, d149119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27916 q ha hb
    | true =>
      simp only [d11369, d146837, d149119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11370 q = 1) (hb : d146837 q = 1) : d149120 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11370, d149120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11370, d149120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11371 q = 1) (hb : d146837 q = 1) : d149121 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11371, d149121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11371, d149121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11372 q = 1) (hb : d146837 q = 1) : d149122 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11372, d149122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11372, d149122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11373 q = 1) (hb : d146837 q = 1) : d149123 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11373, d149123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11373, d149123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11374 q = 1) (hb : d146837 q = 1) : d149124 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11374, d149124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11374, d149124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11375 q = 1) (hb : d146837 q = 1) : d149125 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11375, d149125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11375, d149125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro27918 (p : Pattern) (ha : d11379 p = 1) (hb : d146837 p = 1) : d149129 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11369 q = 1) (hb : d146837 q = 1) : d149119 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11369, d146837, d149119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27916 q ha hb
    | true =>
      simp only [d11369, d146837, d149119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11370 q = 1) (hb : d146837 q = 1) : d149120 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11370, d149120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11370, d149120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11371 q = 1) (hb : d146837 q = 1) : d149121 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11371, d149121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11371, d149121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11373 q = 1) (hb : d146837 q = 1) : d149123 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11373, d149123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11373, d149123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11378 q = 1) (hb : d146837 q = 1) : d149128 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11378, d149128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11378, d149128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11379 q = 1) (hb : d146837 q = 1) : d149129 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11379, d149129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11379, d149129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro27919 (p : Pattern) (ha : d11385 p = 1) (hb : d146837 p = 1) : d149135 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11376 q = 1) (hb : d146837 q = 1) : d149126 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27917 q ha hb
    | true =>
      simp only [d11376, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11377 q = 1) (hb : d146837 q = 1) : d149127 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11380 q = 1) (hb : d146837 q = 1) : d149130 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27918 q ha hb
    | true =>
      simp only [d11380, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11381 q = 1) (hb : d146837 q = 1) : d149131 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11382 q = 1) (hb : d146837 q = 1) : d149132 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11382, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11383 q = 1) (hb : d146837 q = 1) : d149133 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11383, d149133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11383, d149133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11384 q = 1) (hb : d146837 q = 1) : d149134 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11384, d149134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11384, d149134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11385 q = 1) (hb : d146837 q = 1) : d149135 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11385, d149135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11385, d149135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27920 (p : Pattern) (ha : d11389 p = 1) (hb : d146837 p = 1) : d149139 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11380 q = 1) (hb : d146837 q = 1) : d149130 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27918 q ha hb
    | true =>
      simp only [d11380, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11381 q = 1) (hb : d146837 q = 1) : d149131 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11386 q = 1) (hb : d146837 q = 1) : d149136 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11386, d149136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11386, d149136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11387 q = 1) (hb : d146837 q = 1) : d149137 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11387, d149137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11387, d149137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11388 q = 1) (hb : d146837 q = 1) : d149138 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11388, d149138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11388, d149138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11389 q = 1) (hb : d146837 q = 1) : d149139 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11389, d149139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11389, d149139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27921 (p : Pattern) (ha : d11395 p = 1) (hb : d146837 p = 1) : d149145 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11390 q = 1) (hb : d146837 q = 1) : d149140 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11390, d149140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27919 q ha hb
    | true =>
      simp only [d11390, d149140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27920 q ha hb
  have h2 (q : Pattern) (ha : d11391 q = 1) (hb : d146837 q = 1) : d149141 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11391, d149141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11391, d149141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11392 q = 1) (hb : d146837 q = 1) : d149142 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11392, d149142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11392, d149142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11393 q = 1) (hb : d146837 q = 1) : d149143 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11393, d149143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11393, d149143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11394 q = 1) (hb : d146837 q = 1) : d149144 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11394, d149144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11394, d149144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11395 q = 1) (hb : d146837 q = 1) : d149145 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11395, d149145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11395, d149145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27922 (p : Pattern) (ha : d11398 p = 1) (hb : d146837 p = 1) : d149148 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11376 q = 1) (hb : d146837 q = 1) : d149126 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27917 q ha hb
    | true =>
      simp only [d11376, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11377 q = 1) (hb : d146837 q = 1) : d149127 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11380 q = 1) (hb : d146837 q = 1) : d149130 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27918 q ha hb
    | true =>
      simp only [d11380, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11381 q = 1) (hb : d146837 q = 1) : d149131 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11382 q = 1) (hb : d146837 q = 1) : d149132 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11382, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11383 q = 1) (hb : d146837 q = 1) : d149133 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11383, d149133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11383, d149133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11384 q = 1) (hb : d146837 q = 1) : d149134 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11384, d149134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11384, d149134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11398 q = 1) (hb : d146837 q = 1) : d149148 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11398, d149148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11398, d149148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27923 (p : Pattern) (ha : d11399 p = 1) (hb : d146837 p = 1) : d149149 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11380 q = 1) (hb : d146837 q = 1) : d149130 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27918 q ha hb
    | true =>
      simp only [d11380, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11381 q = 1) (hb : d146837 q = 1) : d149131 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11386 q = 1) (hb : d146837 q = 1) : d149136 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11386, d149136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11386, d149136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11387 q = 1) (hb : d146837 q = 1) : d149137 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11387, d149137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11387, d149137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11388 q = 1) (hb : d146837 q = 1) : d149138 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11388, d149138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11388, d149138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11399 q = 1) (hb : d146837 q = 1) : d149149 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11399, d149149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11399, d149149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27924 (p : Pattern) (ha : d11405 p = 1) (hb : d146837 p = 1) : d149155 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11390 q = 1) (hb : d146837 q = 1) : d149140 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11390, d149140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27919 q ha hb
    | true =>
      simp only [d11390, d149140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27920 q ha hb
  have h2 (q : Pattern) (ha : d11391 q = 1) (hb : d146837 q = 1) : d149141 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11391, d149141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11391, d149141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11392 q = 1) (hb : d146837 q = 1) : d149142 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11392, d149142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11392, d149142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11393 q = 1) (hb : d146837 q = 1) : d149143 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11393, d149143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11393, d149143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11394 q = 1) (hb : d146837 q = 1) : d149144 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11394, d149144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11394, d149144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11400 q = 1) (hb : d146837 q = 1) : d149150 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11400, d149150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27922 q ha hb
    | true =>
      simp only [d11400, d149150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27923 q ha hb
  have h7 (q : Pattern) (ha : d11401 q = 1) (hb : d146837 q = 1) : d149151 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11401, d149151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11401, d149151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11402 q = 1) (hb : d146837 q = 1) : d149152 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11402, d149152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11402, d149152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11403 q = 1) (hb : d146837 q = 1) : d149153 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11403, d149153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11403, d149153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11404 q = 1) (hb : d146837 q = 1) : d149154 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11404, d149154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11404, d149154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11405 q = 1) (hb : d146837 q = 1) : d149155 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11405, d149155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11405, d149155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27925 (p : Pattern) (ha : d11513 p = 1) (hb : d146837 p = 1) : d149228 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11390 q = 1) (hb : d146837 q = 1) : d149140 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11390, d149140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27919 q ha hb
    | true =>
      simp only [d11390, d149140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27920 q ha hb
  have h2 (q : Pattern) (ha : d11391 q = 1) (hb : d146837 q = 1) : d149141 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11391, d149141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11391, d149141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11392 q = 1) (hb : d146837 q = 1) : d149142 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11392, d149142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11392, d149142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11393 q = 1) (hb : d146837 q = 1) : d149143 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11393, d149143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11393, d149143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11394 q = 1) (hb : d146837 q = 1) : d149144 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11394, d149144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11394, d149144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11508 q = 1) (hb : d146837 q = 1) : d149223 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11508, d149223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27920 q ha hb
    | true =>
      simp only [d11508, d149223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11509 q = 1) (hb : d146837 q = 1) : d149224 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11509, d149224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11509, d149224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11510 q = 1) (hb : d146837 q = 1) : d149225 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11510, d149225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11510, d149225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11511 q = 1) (hb : d146837 q = 1) : d149226 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11511, d149226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11511, d149226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11512 q = 1) (hb : d146837 q = 1) : d149227 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11512, d149227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11512, d149227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11513 q = 1) (hb : d146837 q = 1) : d149228 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11513, d149228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11513, d149228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27926 (p : Pattern) (ha : d11519 p = 1) (hb : d146837 p = 1) : d149234 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11508 q = 1) (hb : d146837 q = 1) : d149223 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11508, d149223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27920 q ha hb
    | true =>
      simp only [d11508, d149223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11509 q = 1) (hb : d146837 q = 1) : d149224 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11509, d149224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11509, d149224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11510 q = 1) (hb : d146837 q = 1) : d149225 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11510, d149225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11510, d149225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11511 q = 1) (hb : d146837 q = 1) : d149226 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11511, d149226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11511, d149226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11512 q = 1) (hb : d146837 q = 1) : d149227 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11512, d149227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11512, d149227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11514 q = 1) (hb : d146837 q = 1) : d149229 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11514, d149229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27923 q ha hb
    | true =>
      simp only [d11514, d149229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11515 q = 1) (hb : d146837 q = 1) : d149230 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11515, d149230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11515, d149230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11516 q = 1) (hb : d146837 q = 1) : d149231 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11516, d149231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11516, d149231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11517 q = 1) (hb : d146837 q = 1) : d149232 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11517, d149232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11517, d149232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11518 q = 1) (hb : d146837 q = 1) : d149233 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11518, d149233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11518, d149233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11519 q = 1) (hb : d146837 q = 1) : d149234 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11519, d149234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11519, d149234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27927 (p : Pattern) (ha : d11528 p = 1) (hb : d146837 p = 1) : d149243 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11514 q = 1) (hb : d146837 q = 1) : d149229 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11514, d149229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27923 q ha hb
    | true =>
      simp only [d11514, d149229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11515 q = 1) (hb : d146837 q = 1) : d149230 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11515, d149230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11515, d149230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11516 q = 1) (hb : d146837 q = 1) : d149231 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11516, d149231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11516, d149231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11517 q = 1) (hb : d146837 q = 1) : d149232 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11517, d149232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11517, d149232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11518 q = 1) (hb : d146837 q = 1) : d149233 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11518, d149233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11518, d149233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11528 q = 1) (hb : d146837 q = 1) : d149243 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11528, d149243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11528, d149243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27928 (p : Pattern) (ha : d1401 p = 1) (hb : d146836 p = 1) : d149258 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1385 q = 1) (hb : d116750 q = 1) : d22043 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1385, d22043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1385, d22043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19929 q ha hb
  have h2 (q : Pattern) (ha : d1110 q = 1) (hb : d116750 q = 1) : d21742 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19929 q ha hb
    | true =>
      simp only [d1110, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1386 q = 1) (hb : d116750 q = 1) : d22044 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1386, d22044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1386, d22044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1111 q = 1) (hb : d116750 q = 1) : d21743 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1111, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1387 q = 1) (hb : d116750 q = 1) : d22045 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1387, d22045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1387, d22045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1388 q = 1) (hb : d116750 q = 1) : d22046 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1388, d22046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1388, d22046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1391 q = 1) (hb : d116750 q = 1) : d22064 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d22064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1391, d22064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19916 q ha hb
  have h8 (q : Pattern) (ha : d1121 q = 1) (hb : d116750 q = 1) : d21755 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19916 q ha hb
    | true =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1392 q = 1) (hb : d116750 q = 1) : d22065 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d22065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1392, d22065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1122 q = 1) (hb : d116750 q = 1) : d21756 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1393 q = 1) (hb : d116750 q = 1) : d22066 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d22066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1393, d22066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1394 q = 1) (hb : d116750 q = 1) : d22067 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d22067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1394, d22067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1395 q = 1) (hb : d116750 q = 1) : d22068 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1395, d22068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1395, d22068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1400 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d1401 q = 1) (hb : d146836 q = 1) : d149258 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1401, d146836, d149258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1401, d146836, d149258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro27929 (p : Pattern) (ha : d11559 p = 1) (hb : d146837 p = 1) : d149277 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11541 q = 1) (hb : d146837 q = 1) : d149259 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11541, d146837, d149259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27928 q ha hb
    | true =>
      simp only [d11541, d146837, d149259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11542 q = 1) (hb : d146837 q = 1) : d149260 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11542, d149260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11542, d149260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11543 q = 1) (hb : d146837 q = 1) : d149261 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11543, d149261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11543, d149261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11549 q = 1) (hb : d146837 q = 1) : d149267 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11549, d149267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11549, d149267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11558 q = 1) (hb : d146837 q = 1) : d149276 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11558, d149276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11558, d149276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11559 q = 1) (hb : d146837 q = 1) : d149277 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11559, d149277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11559, d149277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro27930 (p : Pattern) (ha : d11615 p = 1) (hb : d146837 p = 1) : d149300 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11560 q = 1) (hb : d146837 q = 1) : d149278 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11560, d149278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27929 q ha hb
    | true =>
      simp only [d11560, d149278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11561 q = 1) (hb : d146837 q = 1) : d149279 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11561, d149279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11561, d149279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11612 q = 1) (hb : d146837 q = 1) : d149297 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11612, d149297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11612, d149297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11613 q = 1) (hb : d146837 q = 1) : d149298 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11613, d149298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11613, d149298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11614 q = 1) (hb : d146837 q = 1) : d149299 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11614, d149299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11614, d149299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11615 q = 1) (hb : d146837 q = 1) : d149300 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11615, d149300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11615, d149300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27931 (p : Pattern) (ha : d11621 p = 1) (hb : d146837 p = 1) : d149306 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11616 q = 1) (hb : d146837 q = 1) : d149301 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11616, d149301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27930 q ha hb
    | true =>
      simp only [d11616, d149301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11617 q = 1) (hb : d146837 q = 1) : d149302 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11617, d149302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11617, d149302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11618 q = 1) (hb : d146837 q = 1) : d149303 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11618, d149303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11618, d149303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11619 q = 1) (hb : d146837 q = 1) : d149304 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11619, d149304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11619, d149304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11620 q = 1) (hb : d146837 q = 1) : d149305 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11620, d149305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11620, d149305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11621 q = 1) (hb : d146837 q = 1) : d149306 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11621, d149306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11621, d149306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27932 (p : Pattern) (ha : d11410 p = 1) (hb : d146837 p = 1) : d149160 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11376 q = 1) (hb : d146837 q = 1) : d149126 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27917 q ha hb
    | true =>
      simp only [d11376, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11377 q = 1) (hb : d146837 q = 1) : d149127 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11380 q = 1) (hb : d146837 q = 1) : d149130 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27918 q ha hb
    | true =>
      simp only [d11380, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11381 q = 1) (hb : d146837 q = 1) : d149131 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11382 q = 1) (hb : d146837 q = 1) : d149132 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11382, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11383 q = 1) (hb : d146837 q = 1) : d149133 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11383, d149133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11383, d149133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11409 q = 1) (hb : d146837 q = 1) : d149159 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11409, d149159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11409, d149159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11410 q = 1) (hb : d146837 q = 1) : d149160 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11410, d149160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11410, d149160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27933 (p : Pattern) (ha : d11412 p = 1) (hb : d146837 p = 1) : d149162 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11380 q = 1) (hb : d146837 q = 1) : d149130 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27918 q ha hb
    | true =>
      simp only [d11380, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11381 q = 1) (hb : d146837 q = 1) : d149131 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11386 q = 1) (hb : d146837 q = 1) : d149136 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11386, d149136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11386, d149136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11387 q = 1) (hb : d146837 q = 1) : d149137 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11387, d149137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11387, d149137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11411 q = 1) (hb : d146837 q = 1) : d149161 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11411, d149161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11411, d149161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11412 q = 1) (hb : d146837 q = 1) : d149162 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11412, d149162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11412, d149162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27934 (p : Pattern) (ha : d11419 p = 1) (hb : d146837 p = 1) : d149169 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11376 q = 1) (hb : d146837 q = 1) : d149126 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27917 q ha hb
    | true =>
      simp only [d11376, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11377 q = 1) (hb : d146837 q = 1) : d149127 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11380 q = 1) (hb : d146837 q = 1) : d149130 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27918 q ha hb
    | true =>
      simp only [d11380, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11381 q = 1) (hb : d146837 q = 1) : d149131 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11382 q = 1) (hb : d146837 q = 1) : d149132 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11382, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11417 q = 1) (hb : d146837 q = 1) : d149167 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11417, d149167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11417, d149167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11418 q = 1) (hb : d146837 q = 1) : d149168 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11418, d149168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11418, d149168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11419 q = 1) (hb : d146837 q = 1) : d149169 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11419, d149169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11419, d149169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27935 (p : Pattern) (ha : d11422 p = 1) (hb : d146837 p = 1) : d149172 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11380 q = 1) (hb : d146837 q = 1) : d149130 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27918 q ha hb
    | true =>
      simp only [d11380, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11381 q = 1) (hb : d146837 q = 1) : d149131 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11386 q = 1) (hb : d146837 q = 1) : d149136 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11386, d149136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11386, d149136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11420 q = 1) (hb : d146837 q = 1) : d149170 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11420, d149170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11420, d149170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11421 q = 1) (hb : d146837 q = 1) : d149171 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11421, d149171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11421, d149171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11422 q = 1) (hb : d146837 q = 1) : d149172 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11422, d149172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11422, d149172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27936 (p : Pattern) (ha : d1209 p = 1) (hb : d116750 p = 1) : d21834 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1208 q = 1) : d1208 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1092 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1209 q = 1) (hb : d116750 q = 1) : d21834 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1209, d116750, d21834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1209, d116750, d21834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro27937 (p : Pattern) (ha : d1215 p = 1) (hb : d146836 p = 1) : d149176 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1210 q = 1) (hb : d116750 q = 1) : d21835 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1210, d21835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27936 q ha hb
    | true =>
      simp only [d1210, d21835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1211 q = 1) (hb : d116750 q = 1) : d21836 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1211, d21836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1211, d21836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1212 q = 1) (hb : d116750 q = 1) : d21837 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1212, d21837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1212, d21837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1213 q = 1) (hb : d116750 q = 1) : d21838 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1213, d21838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1213, d21838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1100 q = 1) (hb : d116750 q = 1) : d21737 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d21737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19945 q ha hb
    | true =>
      simp only [d1100, d21737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1101 q = 1) (hb : d116750 q = 1) : d21738 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d21738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1101, d21738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1102 q = 1) (hb : d116750 q = 1) : d21739 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1102, d21739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1102, d21739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1103 q = 1) (hb : d116750 q = 1) : d21740 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1103, d21740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1103, d21740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1214 q = 1) (hb : d116750 q = 1) : d21839 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1214, d21839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1214, d21839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d1114 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d1215 q = 1) (hb : d146836 q = 1) : d149176 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1215, d146836, d149176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1215, d146836, d149176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro27938 (p : Pattern) (ha : d11431 p = 1) (hb : d146837 p = 1) : d149182 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11426 q = 1) (hb : d146837 q = 1) : d149177 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11426, d146837, d149177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27937 q ha hb
    | true =>
      simp only [d11426, d146837, d149177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11427 q = 1) (hb : d146837 q = 1) : d149178 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11427, d149178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11427, d149178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11428 q = 1) (hb : d146837 q = 1) : d149179 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11428, d149179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11428, d149179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11366 q = 1) (hb : d146837 q = 1) : d149115 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11366, d146837, d149115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27915 q ha hb
    | true =>
      simp only [d11366, d146837, d149115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11367 q = 1) (hb : d146837 q = 1) : d149116 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11367, d149116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11367, d149116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11368 q = 1) (hb : d146837 q = 1) : d149117 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11368, d149117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11368, d149117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11429 q = 1) (hb : d146837 q = 1) : d149180 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11429, d149180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11429, d149180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11369 q = 1) (hb : d146837 q = 1) : d149119 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11369, d146837, d149119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27916 q ha hb
    | true =>
      simp only [d11369, d146837, d149119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d11370 q = 1) (hb : d146837 q = 1) : d149120 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11370, d149120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11370, d149120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11371 q = 1) (hb : d146837 q = 1) : d149121 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11371, d149121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11371, d149121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11372 q = 1) (hb : d146837 q = 1) : d149122 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11372, d149122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11372, d149122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11430 q = 1) (hb : d146837 q = 1) : d149181 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11430, d149181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11430, d149181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11431 q = 1) (hb : d146837 q = 1) : d149182 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11431, d149182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11431, d149182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro27939 (p : Pattern) (ha : d11437 p = 1) (hb : d146837 p = 1) : d149188 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11432 q = 1) (hb : d146837 q = 1) : d149183 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11432, d149183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27938 q ha hb
    | true =>
      simp only [d11432, d149183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11433 q = 1) (hb : d146837 q = 1) : d149184 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11433, d149184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11433, d149184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11376 q = 1) (hb : d146837 q = 1) : d149126 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27917 q ha hb
    | true =>
      simp only [d11376, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11377 q = 1) (hb : d146837 q = 1) : d149127 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11434 q = 1) (hb : d146837 q = 1) : d149185 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11434, d149185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11434, d149185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11435 q = 1) (hb : d146837 q = 1) : d149186 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11435, d149186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11435, d149186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11436 q = 1) (hb : d146837 q = 1) : d149187 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11436, d149187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11436, d149187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11437 q = 1) (hb : d146837 q = 1) : d149188 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11437, d149188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11437, d149188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27940 (p : Pattern) (ha : d5545 p = 1) (hb : d146836 p = 1) : d149118 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1110 q = 1) (hb : d116750 q = 1) : d21742 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19929 q ha hb
    | true =>
      simp only [d1110, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1111 q = 1) (hb : d116750 q = 1) : d21743 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1111, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1112 q = 1) (hb : d116750 q = 1) : d21744 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1112, d21744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1112, d21744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1113 q = 1) (hb : d116750 q = 1) : d21745 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1113, d21745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1113, d21745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1121 q = 1) (hb : d116750 q = 1) : d21755 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19916 q ha hb
    | true =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1122 q = 1) (hb : d116750 q = 1) : d21756 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1123 q = 1) (hb : d116750 q = 1) : d21757 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d21757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1123, d21757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1124 q = 1) (hb : d116750 q = 1) : d21758 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, d21758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1124, d21758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1125 q = 1) (hb : d116750 q = 1) : d21759 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1125, d21759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1125, d21759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d5544 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d5545 q = 1) (hb : d146836 q = 1) : d149118 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5545, d146836, d149118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5545, d146836, d149118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro27941 (p : Pattern) (ha : d11470 p = 1) (hb : d146837 p = 1) : d149125 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11366 q = 1) (hb : d146837 q = 1) : d149115 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11366, d146837, d149115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27915 q ha hb
    | true =>
      simp only [d11366, d146837, d149115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11367 q = 1) (hb : d146837 q = 1) : d149116 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11367, d149116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11367, d149116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11368 q = 1) (hb : d146837 q = 1) : d149117 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11368, d149117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11368, d149117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11369 q = 1) (hb : d146837 q = 1) : d149119 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11369, d146837, d149119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27916 q ha hb
    | true =>
      simp only [d11369, d146837, d149119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11370 q = 1) (hb : d146837 q = 1) : d149120 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11370, d149120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11370, d149120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11371 q = 1) (hb : d146837 q = 1) : d149121 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11371, d149121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11371, d149121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11372 q = 1) (hb : d146837 q = 1) : d149122 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11372, d149122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11372, d149122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11465 q = 1) (hb : d146837 q = 1) : d149119 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11465, d146837, d149119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27940 q ha hb
    | true =>
      simp only [d11465, d146837, d149119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d11466 q = 1) (hb : d146837 q = 1) : d149120 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11466, d149120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11466, d149120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11467 q = 1) (hb : d146837 q = 1) : d149121 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11467, d149121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11467, d149121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11468 q = 1) (hb : d146837 q = 1) : d149123 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11468, d149123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d11468, d149123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d11469 q = 1) (hb : d146837 q = 1) : d149124 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11469, d149124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11469, d149124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11470 q = 1) (hb : d146837 q = 1) : d149125 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11470, d149125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11470, d149125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro27942 (p : Pattern) (ha : d11476 p = 1) (hb : d146837 p = 1) : d149194 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11471 q = 1) (hb : d146837 q = 1) : d149126 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11471, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27941 q ha hb
    | true =>
      simp only [d11471, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11472 q = 1) (hb : d146837 q = 1) : d149127 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11472, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11472, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11473 q = 1) (hb : d146837 q = 1) : d149191 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11473, d149191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11473, d149191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11474 q = 1) (hb : d146837 q = 1) : d149192 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11474, d149192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11474, d149192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11475 q = 1) (hb : d146837 q = 1) : d149193 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11475, d149193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11475, d149193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11476 q = 1) (hb : d146837 q = 1) : d149194 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11476, d149194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11476, d149194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27943 (p : Pattern) (ha : d108942 p = 1) (hb : d146837 p = 1) : d149200 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11413 q = 1) (hb : d146837 q = 1) : d149163 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11413, d149163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27932 q ha hb
    | true =>
      simp only [d11413, d149163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27933 q ha hb
  have h2 (q : Pattern) (ha : d11414 q = 1) (hb : d146837 q = 1) : d149164 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11414, d149164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11414, d149164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11415 q = 1) (hb : d146837 q = 1) : d149165 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11415, d149165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11415, d149165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11416 q = 1) (hb : d146837 q = 1) : d149166 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11416, d149166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11416, d149166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11423 q = 1) (hb : d146837 q = 1) : d149173 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11423, d149173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27934 q ha hb
    | true =>
      simp only [d11423, d149173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27935 q ha hb
  have h6 (q : Pattern) (ha : d11424 q = 1) (hb : d146837 q = 1) : d149174 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11424, d149174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11424, d149174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11425 q = 1) (hb : d146837 q = 1) : d149175 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11425, d149175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11425, d149175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11438 q = 1) (hb : d146837 q = 1) : d149189 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11438, d149189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27939 q ha hb
    | true =>
      simp only [d11438, d149189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27919 q ha hb
  have h9 (q : Pattern) (ha : d108938 q = 1) (hb : d146837 q = 1) : d149190 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108938, d149190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108938, d149190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11477 q = 1) (hb : d146837 q = 1) : d149195 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11477, d149195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27942 q ha hb
    | true =>
      simp only [d11477, d149195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11478 q = 1) (hb : d146837 q = 1) : d149196 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11478, d149196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11478, d149196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d108939 q = 1) (hb : d146837 q = 1) : d149197 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108939, d149197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108939, d149197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108940 q = 1) (hb : d146837 q = 1) : d149198 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108940, d149198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108940, d149198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108941 q = 1) (hb : d146837 q = 1) : d149199 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108941, d149199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108941, d149199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108942 q = 1) (hb : d146837 q = 1) : d149200 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108942, d149200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108942, d149200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro27944 (p : Pattern) (ha : d11483 p = 1) (hb : d146837 p = 1) : d149201 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11376 q = 1) (hb : d146837 q = 1) : d149126 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27917 q ha hb
    | true =>
      simp only [d11376, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11377 q = 1) (hb : d146837 q = 1) : d149127 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11380 q = 1) (hb : d146837 q = 1) : d149130 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27918 q ha hb
    | true =>
      simp only [d11380, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11381 q = 1) (hb : d146837 q = 1) : d149131 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11382 q = 1) (hb : d146837 q = 1) : d149132 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11382, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11383 q = 1) (hb : d146837 q = 1) : d149133 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11383, d149133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11383, d149133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11409 q = 1) (hb : d146837 q = 1) : d149159 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11409, d149159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11409, d149159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11483 q = 1) (hb : d146837 q = 1) : d149201 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11483, d149201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11483, d149201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27945 (p : Pattern) (ha : d11484 p = 1) (hb : d146837 p = 1) : d149202 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11380 q = 1) (hb : d146837 q = 1) : d149130 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27918 q ha hb
    | true =>
      simp only [d11380, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11381 q = 1) (hb : d146837 q = 1) : d149131 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11386 q = 1) (hb : d146837 q = 1) : d149136 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11386, d149136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11386, d149136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11387 q = 1) (hb : d146837 q = 1) : d149137 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11387, d149137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11387, d149137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11411 q = 1) (hb : d146837 q = 1) : d149161 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11411, d149161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11411, d149161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11484 q = 1) (hb : d146837 q = 1) : d149202 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11484, d149202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11484, d149202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27946 (p : Pattern) (ha : d11489 p = 1) (hb : d146837 p = 1) : d149207 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11376 q = 1) (hb : d146837 q = 1) : d149126 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27917 q ha hb
    | true =>
      simp only [d11376, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11377 q = 1) (hb : d146837 q = 1) : d149127 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11380 q = 1) (hb : d146837 q = 1) : d149130 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27918 q ha hb
    | true =>
      simp only [d11380, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11381 q = 1) (hb : d146837 q = 1) : d149131 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11382 q = 1) (hb : d146837 q = 1) : d149132 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11382, d149132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11417 q = 1) (hb : d146837 q = 1) : d149167 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11417, d149167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11417, d149167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11418 q = 1) (hb : d146837 q = 1) : d149168 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11418, d149168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11418, d149168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11489 q = 1) (hb : d146837 q = 1) : d149207 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11489, d149207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11489, d149207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27947 (p : Pattern) (ha : d11490 p = 1) (hb : d146837 p = 1) : d149208 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11380 q = 1) (hb : d146837 q = 1) : d149130 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27918 q ha hb
    | true =>
      simp only [d11380, d149130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11381 q = 1) (hb : d146837 q = 1) : d149131 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d149131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11386 q = 1) (hb : d146837 q = 1) : d149136 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11386, d149136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11386, d149136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11420 q = 1) (hb : d146837 q = 1) : d149170 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11420, d149170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11420, d149170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11421 q = 1) (hb : d146837 q = 1) : d149171 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11421, d149171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11421, d149171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11490 q = 1) (hb : d146837 q = 1) : d149208 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11490, d149208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11490, d149208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27948 (p : Pattern) (ha : d11494 p = 1) (hb : d146837 p = 1) : d149212 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11432 q = 1) (hb : d146837 q = 1) : d149183 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11432, d149183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27938 q ha hb
    | true =>
      simp only [d11432, d149183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11433 q = 1) (hb : d146837 q = 1) : d149184 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11433, d149184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11433, d149184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11376 q = 1) (hb : d146837 q = 1) : d149126 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27917 q ha hb
    | true =>
      simp only [d11376, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11377 q = 1) (hb : d146837 q = 1) : d149127 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11434 q = 1) (hb : d146837 q = 1) : d149185 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11434, d149185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11434, d149185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11435 q = 1) (hb : d146837 q = 1) : d149186 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11435, d149186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11435, d149186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11436 q = 1) (hb : d146837 q = 1) : d149187 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11436, d149187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11436, d149187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11494 q = 1) (hb : d146837 q = 1) : d149212 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11494, d149212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11494, d149212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27949 (p : Pattern) (ha : d11500 p = 1) (hb : d146837 p = 1) : d149215 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11471 q = 1) (hb : d146837 q = 1) : d149126 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11471, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27941 q ha hb
    | true =>
      simp only [d11471, d149126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11472 q = 1) (hb : d146837 q = 1) : d149127 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11472, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11472, d149127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11473 q = 1) (hb : d146837 q = 1) : d149191 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11473, d149191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11473, d149191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11474 q = 1) (hb : d146837 q = 1) : d149192 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11474, d149192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11474, d149192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11475 q = 1) (hb : d146837 q = 1) : d149193 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11475, d149193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11475, d149193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11500 q = 1) (hb : d146837 q = 1) : d149215 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11500, d149215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11500, d149215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27950 (p : Pattern) (ha : d108947 p = 1) (hb : d146837 p = 1) : d149221 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11413 q = 1) (hb : d146837 q = 1) : d149163 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11413, d149163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27932 q ha hb
    | true =>
      simp only [d11413, d149163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27933 q ha hb
  have h2 (q : Pattern) (ha : d11414 q = 1) (hb : d146837 q = 1) : d149164 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11414, d149164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11414, d149164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11415 q = 1) (hb : d146837 q = 1) : d149165 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11415, d149165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11415, d149165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11416 q = 1) (hb : d146837 q = 1) : d149166 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11416, d149166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11416, d149166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11423 q = 1) (hb : d146837 q = 1) : d149173 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11423, d149173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27934 q ha hb
    | true =>
      simp only [d11423, d149173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27935 q ha hb
  have h6 (q : Pattern) (ha : d11424 q = 1) (hb : d146837 q = 1) : d149174 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11424, d149174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11424, d149174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11425 q = 1) (hb : d146837 q = 1) : d149175 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11425, d149175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11425, d149175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11438 q = 1) (hb : d146837 q = 1) : d149189 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11438, d149189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27939 q ha hb
    | true =>
      simp only [d11438, d149189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27919 q ha hb
  have h9 (q : Pattern) (ha : d108938 q = 1) (hb : d146837 q = 1) : d149190 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108938, d149190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108938, d149190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11477 q = 1) (hb : d146837 q = 1) : d149195 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11477, d149195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27942 q ha hb
    | true =>
      simp only [d11477, d149195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11478 q = 1) (hb : d146837 q = 1) : d149196 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11478, d149196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11478, d149196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d108939 q = 1) (hb : d146837 q = 1) : d149197 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108939, d149197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108939, d149197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108940 q = 1) (hb : d146837 q = 1) : d149198 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108940, d149198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108940, d149198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108941 q = 1) (hb : d146837 q = 1) : d149199 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108941, d149199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108941, d149199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d11485 q = 1) (hb : d146837 q = 1) : d149203 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11485, d149203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27944 q ha hb
    | true =>
      simp only [d11485, d149203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27945 q ha hb
  have h16 (q : Pattern) (ha : d11486 q = 1) (hb : d146837 q = 1) : d149204 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11486, d149204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11486, d149204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d11487 q = 1) (hb : d146837 q = 1) : d149205 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11487, d149205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d11487, d149205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d11488 q = 1) (hb : d146837 q = 1) : d149206 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11488, d149206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11488, d149206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d11491 q = 1) (hb : d146837 q = 1) : d149209 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11491, d149209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27946 q ha hb
    | true =>
      simp only [d11491, d149209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27947 q ha hb
  have h20 (q : Pattern) (ha : d11492 q = 1) (hb : d146837 q = 1) : d149210 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11492, d149210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11492, d149210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d11493 q = 1) (hb : d146837 q = 1) : d149211 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11493, d149211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d11493, d149211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d11495 q = 1) (hb : d146837 q = 1) : d149213 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11495, d149213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27948 q ha hb
    | true =>
      simp only [d11495, d149213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27922 q ha hb
  have h23 (q : Pattern) (ha : d108943 q = 1) (hb : d146837 q = 1) : d149214 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108943, d149214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d108943, d149214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d11501 q = 1) (hb : d146837 q = 1) : d149216 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11501, d149216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27949 q ha hb
    | true =>
      simp only [d11501, d149216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d11502 q = 1) (hb : d146837 q = 1) : d149217 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11502, d149217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d11502, d149217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d108944 q = 1) (hb : d146837 q = 1) : d149218 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108944, d149218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d108944, d149218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d108945 q = 1) (hb : d146837 q = 1) : d149219 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108945, d149219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108945, d149219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d108946 q = 1) (hb : d146837 q = 1) : d149220 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108946, d149220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d108946, d149220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d108947 q = 1) (hb : d146837 q = 1) : d149221 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108947, d149221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108947, d149221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro27951 (p : Pattern) (ha : d108954 p = 1) (hb : d146837 p = 1) : d149241 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11495 q = 1) (hb : d146837 q = 1) : d149213 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11495, d149213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27948 q ha hb
    | true =>
      simp only [d11495, d149213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27922 q ha hb
  have h2 (q : Pattern) (ha : d108943 q = 1) (hb : d146837 q = 1) : d149214 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108943, d149214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108943, d149214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11501 q = 1) (hb : d146837 q = 1) : d149216 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11501, d149216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27949 q ha hb
    | true =>
      simp only [d11501, d149216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11502 q = 1) (hb : d146837 q = 1) : d149217 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11502, d149217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11502, d149217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108944 q = 1) (hb : d146837 q = 1) : d149218 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108944, d149218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108944, d149218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108952 q = 1) (hb : d146837 q = 1) : d149239 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108952, d149239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108952, d149239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108953 q = 1) (hb : d146837 q = 1) : d149240 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108953, d149240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108953, d149240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108954 q = 1) (hb : d146837 q = 1) : d149241 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108954, d149241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108954, d149241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27952 (p : Pattern) (ha : d1390 p = 1) (hb : d146836 p = 1) : d149249 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1376 q = 1) (hb : d116750 q = 1) : d22024 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1376, d22024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1376, d22024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27936 q ha hb
  have h2 (q : Pattern) (ha : d1210 q = 1) (hb : d116750 q = 1) : d21835 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1210, d21835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27936 q ha hb
    | true =>
      simp only [d1210, d21835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1377 q = 1) (hb : d116750 q = 1) : d22025 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1377, d22025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1377, d22025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1211 q = 1) (hb : d116750 q = 1) : d21836 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1211, d21836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1211, d21836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1378 q = 1) (hb : d116750 q = 1) : d22026 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1378, d22026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1378, d22026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1379 q = 1) (hb : d116750 q = 1) : d22027 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1379, d22027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1379, d22027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1380 q = 1) (hb : d116750 q = 1) : d22028 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1380, d22028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1380, d22028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19945 q ha hb
  have h8 (q : Pattern) (ha : d1100 q = 1) (hb : d116750 q = 1) : d21737 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d21737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19945 q ha hb
    | true =>
      simp only [d1100, d21737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1381 q = 1) (hb : d116750 q = 1) : d22029 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1381, d22029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1381, d22029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1101 q = 1) (hb : d116750 q = 1) : d21738 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d21738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1101, d21738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1382 q = 1) (hb : d116750 q = 1) : d22030 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1382, d22030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1382, d22030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1383 q = 1) (hb : d116750 q = 1) : d22031 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1383, d22031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1383, d22031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1384 q = 1) (hb : d116750 q = 1) : d22032 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1384, d22032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1384, d22032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1389 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d1390 q = 1) (hb : d146836 q = 1) : d149249 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1390, d146836, d149249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1390, d146836, d149249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro27953 (p : Pattern) (ha : d1396 p = 1) (hb : d146836 p = 1) : d149253 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1380 q = 1) (hb : d116750 q = 1) : d22028 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1380, d22028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1380, d22028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19945 q ha hb
  have h2 (q : Pattern) (ha : d1100 q = 1) (hb : d116750 q = 1) : d21737 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d21737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19945 q ha hb
    | true =>
      simp only [d1100, d21737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1381 q = 1) (hb : d116750 q = 1) : d22029 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1381, d22029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1381, d22029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1101 q = 1) (hb : d116750 q = 1) : d21738 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d21738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1101, d21738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1382 q = 1) (hb : d116750 q = 1) : d22030 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1382, d22030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1382, d22030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1383 q = 1) (hb : d116750 q = 1) : d22031 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1383, d22031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1383, d22031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1385 q = 1) (hb : d116750 q = 1) : d22043 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1385, d22043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1385, d22043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19929 q ha hb
  have h8 (q : Pattern) (ha : d1110 q = 1) (hb : d116750 q = 1) : d21742 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19929 q ha hb
    | true =>
      simp only [d1110, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1386 q = 1) (hb : d116750 q = 1) : d22044 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1386, d22044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1386, d22044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1111 q = 1) (hb : d116750 q = 1) : d21743 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1111, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1387 q = 1) (hb : d116750 q = 1) : d22045 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1387, d22045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1387, d22045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1388 q = 1) (hb : d116750 q = 1) : d22046 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1388, d22046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1388, d22046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1389 q = 1) (hb : d116750 q = 1) : d22047 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1389, d22047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1389, d22047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1395 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d1396 q = 1) (hb : d146836 q = 1) : d149253 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1396, d146836, d149253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1396, d146836, d149253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro27954 (p : Pattern) (ha : d11546 p = 1) (hb : d146837 p = 1) : d149264 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11534 q = 1) (hb : d146837 q = 1) : d149250 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11534, d146837, d149250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27952 q ha hb
    | true =>
      simp only [d11534, d146837, d149250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11535 q = 1) (hb : d146837 q = 1) : d149251 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11535, d149251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11535, d149251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11536 q = 1) (hb : d146837 q = 1) : d149252 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11536, d149252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11536, d149252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11537 q = 1) (hb : d146837 q = 1) : d149254 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11537, d146837, d149254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27953 q ha hb
    | true =>
      simp only [d11537, d146837, d149254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11538 q = 1) (hb : d146837 q = 1) : d149255 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11538, d149255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11538, d149255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11539 q = 1) (hb : d146837 q = 1) : d149256 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11539, d149256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11539, d149256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11540 q = 1) (hb : d146837 q = 1) : d149257 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11540, d149257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11540, d149257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11541 q = 1) (hb : d146837 q = 1) : d149259 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11541, d146837, d149259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27928 q ha hb
    | true =>
      simp only [d11541, d146837, d149259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d11542 q = 1) (hb : d146837 q = 1) : d149260 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11542, d149260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11542, d149260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11543 q = 1) (hb : d146837 q = 1) : d149261 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11543, d149261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11543, d149261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11544 q = 1) (hb : d146837 q = 1) : d149262 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11544, d149262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11544, d149262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11545 q = 1) (hb : d146837 q = 1) : d149263 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11545, d149263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11545, d149263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11546 q = 1) (hb : d146837 q = 1) : d149264 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11546, d149264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11546, d149264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro27955 (p : Pattern) (ha : d11551 p = 1) (hb : d146837 p = 1) : d149269 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11537 q = 1) (hb : d146837 q = 1) : d149254 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11537, d146837, d149254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27953 q ha hb
    | true =>
      simp only [d11537, d146837, d149254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11538 q = 1) (hb : d146837 q = 1) : d149255 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11538, d149255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11538, d149255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11539 q = 1) (hb : d146837 q = 1) : d149256 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11539, d149256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11539, d149256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11541 q = 1) (hb : d146837 q = 1) : d149259 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11541, d146837, d149259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27928 q ha hb
    | true =>
      simp only [d11541, d146837, d149259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11542 q = 1) (hb : d146837 q = 1) : d149260 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11542, d149260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11542, d149260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11543 q = 1) (hb : d146837 q = 1) : d149261 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11543, d149261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11543, d149261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11544 q = 1) (hb : d146837 q = 1) : d149262 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11544, d149262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11544, d149262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11549 q = 1) (hb : d146837 q = 1) : d149267 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11549, d149267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11549, d149267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11550 q = 1) (hb : d146837 q = 1) : d149268 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11550, d149268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11550, d149268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11551 q = 1) (hb : d146837 q = 1) : d149269 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11551, d149269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11551, d149269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro27956 (p : Pattern) (ha : d11557 p = 1) (hb : d146837 p = 1) : d149275 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11547 q = 1) (hb : d146837 q = 1) : d149265 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11547, d149265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27954 q ha hb
    | true =>
      simp only [d11547, d149265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11548 q = 1) (hb : d146837 q = 1) : d149266 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11548, d149266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11548, d149266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11552 q = 1) (hb : d146837 q = 1) : d149270 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11552, d149270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27955 q ha hb
    | true =>
      simp only [d11552, d149270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11553 q = 1) (hb : d146837 q = 1) : d149271 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11553, d149271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11553, d149271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11554 q = 1) (hb : d146837 q = 1) : d149272 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11554, d149272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11554, d149272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11555 q = 1) (hb : d146837 q = 1) : d149273 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11555, d149273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11555, d149273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11556 q = 1) (hb : d146837 q = 1) : d149274 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11556, d149274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11556, d149274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11557 q = 1) (hb : d146837 q = 1) : d149275 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11557, d149275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11557, d149275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27957 (p : Pattern) (ha : d11565 p = 1) (hb : d146837 p = 1) : d149283 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11552 q = 1) (hb : d146837 q = 1) : d149270 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11552, d149270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27955 q ha hb
    | true =>
      simp only [d11552, d149270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11553 q = 1) (hb : d146837 q = 1) : d149271 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11553, d149271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11553, d149271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11560 q = 1) (hb : d146837 q = 1) : d149278 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11560, d149278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27929 q ha hb
    | true =>
      simp only [d11560, d149278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11561 q = 1) (hb : d146837 q = 1) : d149279 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11561, d149279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11561, d149279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11562 q = 1) (hb : d146837 q = 1) : d149280 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11562, d149280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11562, d149280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11563 q = 1) (hb : d146837 q = 1) : d149281 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11563, d149281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11563, d149281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11564 q = 1) (hb : d146837 q = 1) : d149282 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11564, d149282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11564, d149282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11565 q = 1) (hb : d146837 q = 1) : d149283 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11565, d149283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11565, d149283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27958 (p : Pattern) (ha : d5589 p = 1) (hb : d146836 p = 1) : d149258 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1385 q = 1) (hb : d116750 q = 1) : d22043 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1385, d22043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1385, d22043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19929 q ha hb
  have h2 (q : Pattern) (ha : d1110 q = 1) (hb : d116750 q = 1) : d21742 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19929 q ha hb
    | true =>
      simp only [d1110, d21742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1386 q = 1) (hb : d116750 q = 1) : d22044 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1386, d22044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1386, d22044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1111 q = 1) (hb : d116750 q = 1) : d21743 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1111, d21743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1387 q = 1) (hb : d116750 q = 1) : d22045 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1387, d22045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1387, d22045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1388 q = 1) (hb : d116750 q = 1) : d22046 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1388, d22046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1388, d22046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1391 q = 1) (hb : d116750 q = 1) : d22064 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d22064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1391, d22064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19916 q ha hb
  have h8 (q : Pattern) (ha : d1121 q = 1) (hb : d116750 q = 1) : d21755 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19916 q ha hb
    | true =>
      simp only [d1121, d21755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1392 q = 1) (hb : d116750 q = 1) : d22065 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d22065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1392, d22065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1122 q = 1) (hb : d116750 q = 1) : d21756 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1122, d21756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1393 q = 1) (hb : d116750 q = 1) : d22066 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d22066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1393, d22066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1394 q = 1) (hb : d116750 q = 1) : d22067 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d22067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1394, d22067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1395 q = 1) (hb : d116750 q = 1) : d22068 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1395, d22068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1395, d22068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d5588 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d5589 q = 1) (hb : d146836 q = 1) : d149258 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5589, d146836, d149258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5589, d146836, d149258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro27959 (p : Pattern) (ha : d11598 p = 1) (hb : d146837 p = 1) : d149269 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11537 q = 1) (hb : d146837 q = 1) : d149254 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11537, d146837, d149254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27953 q ha hb
    | true =>
      simp only [d11537, d146837, d149254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11538 q = 1) (hb : d146837 q = 1) : d149255 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11538, d149255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11538, d149255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11539 q = 1) (hb : d146837 q = 1) : d149256 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11539, d149256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11539, d149256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11541 q = 1) (hb : d146837 q = 1) : d149259 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11541, d146837, d149259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27928 q ha hb
    | true =>
      simp only [d11541, d146837, d149259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11542 q = 1) (hb : d146837 q = 1) : d149260 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11542, d149260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11542, d149260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11543 q = 1) (hb : d146837 q = 1) : d149261 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11543, d149261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11543, d149261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11544 q = 1) (hb : d146837 q = 1) : d149262 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11544, d149262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11544, d149262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11593 q = 1) (hb : d146837 q = 1) : d149259 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11593, d146837, d149259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27958 q ha hb
    | true =>
      simp only [d11593, d146837, d149259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d11594 q = 1) (hb : d146837 q = 1) : d149260 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11594, d149260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11594, d149260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11595 q = 1) (hb : d146837 q = 1) : d149261 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11595, d149261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11595, d149261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11596 q = 1) (hb : d146837 q = 1) : d149267 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11596, d149267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d11596, d149267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d11597 q = 1) (hb : d146837 q = 1) : d149268 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11597, d149268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11597, d149268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11598 q = 1) (hb : d146837 q = 1) : d149269 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11598, d149269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11598, d149269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro27960 (p : Pattern) (ha : d11604 p = 1) (hb : d146837 p = 1) : d149289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11599 q = 1) (hb : d146837 q = 1) : d149270 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11599, d149270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27959 q ha hb
    | true =>
      simp only [d11599, d149270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11600 q = 1) (hb : d146837 q = 1) : d149271 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11600, d149271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11600, d149271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11601 q = 1) (hb : d146837 q = 1) : d149286 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11601, d149286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11601, d149286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11602 q = 1) (hb : d146837 q = 1) : d149287 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11602, d149287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11602, d149287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11603 q = 1) (hb : d146837 q = 1) : d149288 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11603, d149288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11603, d149288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11604 q = 1) (hb : d146837 q = 1) : d149289 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11604, d149289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11604, d149289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27961 (p : Pattern) (ha : d108964 p = 1) (hb : d146837 p = 1) : d149295 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11566 q = 1) (hb : d146837 q = 1) : d149284 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11566, d149284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27956 q ha hb
    | true =>
      simp only [d11566, d149284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27957 q ha hb
  have h2 (q : Pattern) (ha : d108960 q = 1) (hb : d146837 q = 1) : d149285 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108960, d149285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108960, d149285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11605 q = 1) (hb : d146837 q = 1) : d149290 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11605, d149290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27960 q ha hb
    | true =>
      simp only [d11605, d149290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11606 q = 1) (hb : d146837 q = 1) : d149291 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11606, d149291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11606, d149291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108961 q = 1) (hb : d146837 q = 1) : d149292 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108961, d149292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108961, d149292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108962 q = 1) (hb : d146837 q = 1) : d149293 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108962, d149293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108962, d149293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108963 q = 1) (hb : d146837 q = 1) : d149294 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108963, d149294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108963, d149294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108964 q = 1) (hb : d146837 q = 1) : d149295 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108964, d149295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108964, d149295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27962 (p : Pattern) (ha : d108970 p = 1) (hb : d146837 p = 1) : d149312 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11396 q = 1) (hb : d146837 q = 1) : d149146 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11396, d149146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11396, d149146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27921 q ha hb
  have h2 (q : Pattern) (ha : d11397 q = 1) (hb : d146837 q = 1) : d149147 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11397, d149147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11397, d149147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11406 q = 1) (hb : d146837 q = 1) : d149156 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11406, d149156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27921 q ha hb
    | true =>
      simp only [d11406, d149156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27924 q ha hb
  have h4 (q : Pattern) (ha : d11407 q = 1) (hb : d146837 q = 1) : d149157 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11407, d149157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11407, d149157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11408 q = 1) (hb : d146837 q = 1) : d149158 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11408, d149158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11408, d149158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108948 q = 1) (hb : d146837 q = 1) : d149222 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108948, d149222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27943 q ha hb
    | true =>
      simp only [d108948, d149222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27950 q ha hb
  have h7 (q : Pattern) (ha : d11520 q = 1) (hb : d146837 q = 1) : d149235 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11520, d149235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27925 q ha hb
    | true =>
      simp only [d11520, d149235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27926 q ha hb
  have h8 (q : Pattern) (ha : d108949 q = 1) (hb : d146837 q = 1) : d149236 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108949, d149236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108949, d149236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108950 q = 1) (hb : d146837 q = 1) : d149237 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108950, d149237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108950, d149237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d108951 q = 1) (hb : d146837 q = 1) : d149238 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108951, d149238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108951, d149238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108955 q = 1) (hb : d146837 q = 1) : d149242 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108955, d149242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108955, d149242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27951 q ha hb
  have h12 (q : Pattern) (ha : d11529 q = 1) (hb : d146837 q = 1) : d149244 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11529, d149244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11529, d149244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27927 q ha hb
  have h13 (q : Pattern) (ha : d108956 q = 1) (hb : d146837 q = 1) : d149245 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108956, d149245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108956, d149245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108957 q = 1) (hb : d146837 q = 1) : d149246 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108957, d149246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108957, d149246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d108958 q = 1) (hb : d146837 q = 1) : d149247 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108958, d149247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108958, d149247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d108959 q = 1) (hb : d146837 q = 1) : d149248 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108959, d149248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108959, d149248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108965 q = 1) (hb : d146837 q = 1) : d149296 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108965, d149296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108965, d149296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27961 q ha hb
  have h18 (q : Pattern) (ha : d11622 q = 1) (hb : d146837 q = 1) : d149307 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11622, d149307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11622, d149307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27931 q ha hb
  have h19 (q : Pattern) (ha : d108966 q = 1) (hb : d146837 q = 1) : d149308 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108966, d149308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108966, d149308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d108967 q = 1) (hb : d146837 q = 1) : d149309 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108967, d149309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d108967, d149309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d108968 q = 1) (hb : d146837 q = 1) : d149310 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108968, d149310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d108968, d149310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d108969 q = 1) (hb : d146837 q = 1) : d149311 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108969, d149311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108969, d149311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d108970 q = 1) (hb : d146837 q = 1) : d149312 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108970, d149312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108970, d149312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro27963 (p : Pattern) (ha : d108976 p = 1) (hb : d146837 p = 1) : d149318 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108971 q = 1) (hb : d146837 q = 1) : d149313 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108971, d149313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108971, d149313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27962 q ha hb
  have h2 (q : Pattern) (ha : d108972 q = 1) (hb : d146837 q = 1) : d149314 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108972, d149314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108972, d149314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108973 q = 1) (hb : d146837 q = 1) : d149315 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108973, d149315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108973, d149315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108974 q = 1) (hb : d146837 q = 1) : d149316 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108974, d149316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108974, d149316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108975 q = 1) (hb : d146837 q = 1) : d149317 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108975, d149317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108975, d149317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108976 q = 1) (hb : d146837 q = 1) : d149318 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108976, d149318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108976, d149318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27964 (p : Pattern) (ha : d1587 p = 1) (hb : d146836 p = 1) : d149322 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1555 q = 1) (hb : d116750 q = 1) : d10036 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d10036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20002 q ha hb
    | true =>
      simp only [d1555, d10036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1556 q = 1) (hb : d116750 q = 1) : d10038 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d10038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1556, d10038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1557 q = 1) (hb : d116750 q = 1) : d16859 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1557, d16859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1557, d16859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1558 q = 1) (hb : d116750 q = 1) : d16860 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1558, d16860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1558, d16860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1570 q = 1) (hb : d116750 q = 1) : d22220 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d22220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19986 q ha hb
    | true =>
      simp only [d1570, d22220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1571 q = 1) (hb : d116750 q = 1) : d22221 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d22221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1571, d22221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1572 q = 1) (hb : d116750 q = 1) : d22222 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1572, d22222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1572, d22222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1573 q = 1) (hb : d116750 q = 1) : d22223 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1573, d22223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1573, d22223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1574 q = 1) (hb : d116750 q = 1) : d22224 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1574, d22224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1574, d22224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d1586 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d1587 q = 1) (hb : d146836 q = 1) : d149322 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1587, d146836, d149322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1587, d146836, d149322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro27965 (p : Pattern) (ha : d1589 p = 1) (hb : d146836 p = 1) : d149326 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1570 q = 1) (hb : d116750 q = 1) : d22220 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d22220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19986 q ha hb
    | true =>
      simp only [d1570, d22220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1571 q = 1) (hb : d116750 q = 1) : d22221 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d22221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1571, d22221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1572 q = 1) (hb : d116750 q = 1) : d22222 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1572, d22222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1572, d22222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1573 q = 1) (hb : d116750 q = 1) : d22223 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1573, d22223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1573, d22223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1582 q = 1) (hb : d116750 q = 1) : d22233 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d22233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19973 q ha hb
    | true =>
      simp only [d1582, d22233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1583 q = 1) (hb : d116750 q = 1) : d22234 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d22234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1583, d22234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1584 q = 1) (hb : d116750 q = 1) : d22235 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1584, d22235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1584, d22235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1585 q = 1) (hb : d116750 q = 1) : d22236 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1585, d22236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1585, d22236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1586 q = 1) (hb : d116750 q = 1) : d22237 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1586, d22237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1586, d22237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d1588 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d1589 q = 1) (hb : d146836 q = 1) : d149326 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1589, d146836, d149326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1589, d146836, d149326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro27966 (p : Pattern) (ha : d11646 p = 1) (hb : d146837 p = 1) : d149333 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11637 q = 1) (hb : d146837 q = 1) : d149323 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11637, d146837, d149323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27964 q ha hb
    | true =>
      simp only [d11637, d146837, d149323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11638 q = 1) (hb : d146837 q = 1) : d149324 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11638, d149324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11638, d149324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11639 q = 1) (hb : d146837 q = 1) : d149325 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11639, d149325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11639, d149325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11640 q = 1) (hb : d146837 q = 1) : d149327 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11640, d146837, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27965 q ha hb
    | true =>
      simp only [d11640, d146837, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11641 q = 1) (hb : d146837 q = 1) : d149328 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11641, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11641, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11642 q = 1) (hb : d146837 q = 1) : d149329 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11642, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11642, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11643 q = 1) (hb : d146837 q = 1) : d149330 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11643, d149330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11643, d149330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11644 q = 1) (hb : d146837 q = 1) : d149331 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11644, d149331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11644, d149331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11645 q = 1) (hb : d146837 q = 1) : d149332 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11645, d149332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11645, d149332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11646 q = 1) (hb : d146837 q = 1) : d149333 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11646, d149333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11646, d149333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro27967 (p : Pattern) (ha : d11650 p = 1) (hb : d146837 p = 1) : d149337 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11640 q = 1) (hb : d146837 q = 1) : d149327 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11640, d146837, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27965 q ha hb
    | true =>
      simp only [d11640, d146837, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11641 q = 1) (hb : d146837 q = 1) : d149328 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11641, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11641, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11642 q = 1) (hb : d146837 q = 1) : d149329 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11642, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11642, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11644 q = 1) (hb : d146837 q = 1) : d149331 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11644, d149331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11644, d149331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11649 q = 1) (hb : d146837 q = 1) : d149336 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11649, d149336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11649, d149336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11650 q = 1) (hb : d146837 q = 1) : d149337 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11650, d149337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11650, d149337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro27968 (p : Pattern) (ha : d11656 p = 1) (hb : d146837 p = 1) : d149343 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11647 q = 1) (hb : d146837 q = 1) : d149334 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27966 q ha hb
    | true =>
      simp only [d11647, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11648 q = 1) (hb : d146837 q = 1) : d149335 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11651 q = 1) (hb : d146837 q = 1) : d149338 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27967 q ha hb
    | true =>
      simp only [d11651, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11652 q = 1) (hb : d146837 q = 1) : d149339 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11653 q = 1) (hb : d146837 q = 1) : d149340 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11653, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11654 q = 1) (hb : d146837 q = 1) : d149341 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11654, d149341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11654, d149341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11655 q = 1) (hb : d146837 q = 1) : d149342 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11655, d149342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11655, d149342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11656 q = 1) (hb : d146837 q = 1) : d149343 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11656, d149343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11656, d149343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27969 (p : Pattern) (ha : d11660 p = 1) (hb : d146837 p = 1) : d149347 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11651 q = 1) (hb : d146837 q = 1) : d149338 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27967 q ha hb
    | true =>
      simp only [d11651, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11652 q = 1) (hb : d146837 q = 1) : d149339 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11657 q = 1) (hb : d146837 q = 1) : d149344 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11657, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11657, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11658 q = 1) (hb : d146837 q = 1) : d149345 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11658, d149345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11658, d149345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11659 q = 1) (hb : d146837 q = 1) : d149346 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11659, d149346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11659, d149346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11660 q = 1) (hb : d146837 q = 1) : d149347 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11660, d149347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11660, d149347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27970 (p : Pattern) (ha : d11666 p = 1) (hb : d146837 p = 1) : d149353 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11661 q = 1) (hb : d146837 q = 1) : d149348 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11661, d149348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27968 q ha hb
    | true =>
      simp only [d11661, d149348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27969 q ha hb
  have h2 (q : Pattern) (ha : d11662 q = 1) (hb : d146837 q = 1) : d149349 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11662, d149349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11662, d149349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11663 q = 1) (hb : d146837 q = 1) : d149350 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11663, d149350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11663, d149350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11664 q = 1) (hb : d146837 q = 1) : d149351 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11664, d149351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11664, d149351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11665 q = 1) (hb : d146837 q = 1) : d149352 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11665, d149352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11665, d149352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11666 q = 1) (hb : d146837 q = 1) : d149353 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11666, d149353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11666, d149353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27971 (p : Pattern) (ha : d11669 p = 1) (hb : d146837 p = 1) : d149356 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11647 q = 1) (hb : d146837 q = 1) : d149334 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27966 q ha hb
    | true =>
      simp only [d11647, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11648 q = 1) (hb : d146837 q = 1) : d149335 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11651 q = 1) (hb : d146837 q = 1) : d149338 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27967 q ha hb
    | true =>
      simp only [d11651, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11652 q = 1) (hb : d146837 q = 1) : d149339 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11653 q = 1) (hb : d146837 q = 1) : d149340 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11653, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11654 q = 1) (hb : d146837 q = 1) : d149341 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11654, d149341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11654, d149341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11655 q = 1) (hb : d146837 q = 1) : d149342 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11655, d149342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11655, d149342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11669 q = 1) (hb : d146837 q = 1) : d149356 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11669, d149356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11669, d149356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27972 (p : Pattern) (ha : d11670 p = 1) (hb : d146837 p = 1) : d149357 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11651 q = 1) (hb : d146837 q = 1) : d149338 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27967 q ha hb
    | true =>
      simp only [d11651, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11652 q = 1) (hb : d146837 q = 1) : d149339 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11657 q = 1) (hb : d146837 q = 1) : d149344 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11657, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11657, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11658 q = 1) (hb : d146837 q = 1) : d149345 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11658, d149345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11658, d149345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11659 q = 1) (hb : d146837 q = 1) : d149346 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11659, d149346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11659, d149346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11670 q = 1) (hb : d146837 q = 1) : d149357 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11670, d149357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11670, d149357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27973 (p : Pattern) (ha : d11676 p = 1) (hb : d146837 p = 1) : d149363 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11661 q = 1) (hb : d146837 q = 1) : d149348 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11661, d149348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27968 q ha hb
    | true =>
      simp only [d11661, d149348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27969 q ha hb
  have h2 (q : Pattern) (ha : d11662 q = 1) (hb : d146837 q = 1) : d149349 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11662, d149349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11662, d149349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11663 q = 1) (hb : d146837 q = 1) : d149350 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11663, d149350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11663, d149350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11664 q = 1) (hb : d146837 q = 1) : d149351 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11664, d149351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11664, d149351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11665 q = 1) (hb : d146837 q = 1) : d149352 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11665, d149352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11665, d149352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11671 q = 1) (hb : d146837 q = 1) : d149358 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11671, d149358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27971 q ha hb
    | true =>
      simp only [d11671, d149358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27972 q ha hb
  have h7 (q : Pattern) (ha : d11672 q = 1) (hb : d146837 q = 1) : d149359 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11672, d149359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11672, d149359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11673 q = 1) (hb : d146837 q = 1) : d149360 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11673, d149360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11673, d149360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11674 q = 1) (hb : d146837 q = 1) : d149361 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11674, d149361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11674, d149361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11675 q = 1) (hb : d146837 q = 1) : d149362 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11675, d149362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11675, d149362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11676 q = 1) (hb : d146837 q = 1) : d149363 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11676, d149363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11676, d149363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27974 (p : Pattern) (ha : d11784 p = 1) (hb : d146837 p = 1) : d149436 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11661 q = 1) (hb : d146837 q = 1) : d149348 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11661, d149348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27968 q ha hb
    | true =>
      simp only [d11661, d149348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27969 q ha hb
  have h2 (q : Pattern) (ha : d11662 q = 1) (hb : d146837 q = 1) : d149349 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11662, d149349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11662, d149349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11663 q = 1) (hb : d146837 q = 1) : d149350 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11663, d149350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11663, d149350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11664 q = 1) (hb : d146837 q = 1) : d149351 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11664, d149351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11664, d149351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11665 q = 1) (hb : d146837 q = 1) : d149352 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11665, d149352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11665, d149352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11779 q = 1) (hb : d146837 q = 1) : d149431 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11779, d149431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27969 q ha hb
    | true =>
      simp only [d11779, d149431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11780 q = 1) (hb : d146837 q = 1) : d149432 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11780, d149432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11780, d149432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11781 q = 1) (hb : d146837 q = 1) : d149433 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11781, d149433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11781, d149433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11782 q = 1) (hb : d146837 q = 1) : d149434 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11782, d149434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11782, d149434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11783 q = 1) (hb : d146837 q = 1) : d149435 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11783, d149435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11783, d149435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11784 q = 1) (hb : d146837 q = 1) : d149436 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11784, d149436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11784, d149436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27975 (p : Pattern) (ha : d11790 p = 1) (hb : d146837 p = 1) : d149442 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11779 q = 1) (hb : d146837 q = 1) : d149431 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11779, d149431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27969 q ha hb
    | true =>
      simp only [d11779, d149431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11780 q = 1) (hb : d146837 q = 1) : d149432 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11780, d149432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11780, d149432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11781 q = 1) (hb : d146837 q = 1) : d149433 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11781, d149433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11781, d149433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11782 q = 1) (hb : d146837 q = 1) : d149434 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11782, d149434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11782, d149434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11783 q = 1) (hb : d146837 q = 1) : d149435 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11783, d149435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11783, d149435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11785 q = 1) (hb : d146837 q = 1) : d149437 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11785, d149437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27972 q ha hb
    | true =>
      simp only [d11785, d149437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11786 q = 1) (hb : d146837 q = 1) : d149438 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11786, d149438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11786, d149438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11787 q = 1) (hb : d146837 q = 1) : d149439 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11787, d149439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11787, d149439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11788 q = 1) (hb : d146837 q = 1) : d149440 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11788, d149440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11788, d149440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11789 q = 1) (hb : d146837 q = 1) : d149441 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11789, d149441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11789, d149441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11790 q = 1) (hb : d146837 q = 1) : d149442 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11790, d149442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11790, d149442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27976 (p : Pattern) (ha : d11799 p = 1) (hb : d146837 p = 1) : d149451 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11785 q = 1) (hb : d146837 q = 1) : d149437 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11785, d149437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27972 q ha hb
    | true =>
      simp only [d11785, d149437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11786 q = 1) (hb : d146837 q = 1) : d149438 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11786, d149438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11786, d149438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11787 q = 1) (hb : d146837 q = 1) : d149439 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11787, d149439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11787, d149439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11788 q = 1) (hb : d146837 q = 1) : d149440 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11788, d149440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11788, d149440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11789 q = 1) (hb : d146837 q = 1) : d149441 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11789, d149441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11789, d149441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11799 q = 1) (hb : d146837 q = 1) : d149451 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11799, d149451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11799, d149451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27977 (p : Pattern) (ha : d1878 p = 1) (hb : d146836 p = 1) : d149466 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1862 q = 1) (hb : d116750 q = 1) : d22508 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1862, d22508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1862, d22508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19986 q ha hb
  have h2 (q : Pattern) (ha : d1570 q = 1) (hb : d116750 q = 1) : d22220 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d22220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19986 q ha hb
    | true =>
      simp only [d1570, d22220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1863 q = 1) (hb : d116750 q = 1) : d22509 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1863, d22509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1863, d22509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1571 q = 1) (hb : d116750 q = 1) : d22221 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d22221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1571, d22221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1864 q = 1) (hb : d116750 q = 1) : d22510 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1864, d22510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1864, d22510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1865 q = 1) (hb : d116750 q = 1) : d22511 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1865, d22511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1865, d22511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1868 q = 1) (hb : d116750 q = 1) : d22529 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, d22529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1868, d22529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19973 q ha hb
  have h8 (q : Pattern) (ha : d1582 q = 1) (hb : d116750 q = 1) : d22233 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d22233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19973 q ha hb
    | true =>
      simp only [d1582, d22233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1869 q = 1) (hb : d116750 q = 1) : d22530 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, d22530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1869, d22530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1583 q = 1) (hb : d116750 q = 1) : d22234 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d22234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1583, d22234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1870 q = 1) (hb : d116750 q = 1) : d22531 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1870, d22531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1870, d22531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1871 q = 1) (hb : d116750 q = 1) : d22532 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1871, d22532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1871, d22532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1872 q = 1) (hb : d116750 q = 1) : d22533 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1872, d22533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1872, d22533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1877 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d1878 q = 1) (hb : d146836 q = 1) : d149466 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1878, d146836, d149466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1878, d146836, d149466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro27978 (p : Pattern) (ha : d11830 p = 1) (hb : d146837 p = 1) : d149485 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11812 q = 1) (hb : d146837 q = 1) : d149467 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11812, d146837, d149467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27977 q ha hb
    | true =>
      simp only [d11812, d146837, d149467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11813 q = 1) (hb : d146837 q = 1) : d149468 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11813, d149468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11813, d149468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11814 q = 1) (hb : d146837 q = 1) : d149469 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11814, d149469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11814, d149469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11820 q = 1) (hb : d146837 q = 1) : d149475 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11820, d149475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11820, d149475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11829 q = 1) (hb : d146837 q = 1) : d149484 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11829, d149484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11829, d149484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11830 q = 1) (hb : d146837 q = 1) : d149485 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11830, d149485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11830, d149485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro27979 (p : Pattern) (ha : d11886 p = 1) (hb : d146837 p = 1) : d149508 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11831 q = 1) (hb : d146837 q = 1) : d149486 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11831, d149486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27978 q ha hb
    | true =>
      simp only [d11831, d149486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11832 q = 1) (hb : d146837 q = 1) : d149487 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11832, d149487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11832, d149487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11883 q = 1) (hb : d146837 q = 1) : d149505 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11883, d149505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11883, d149505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11884 q = 1) (hb : d146837 q = 1) : d149506 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11884, d149506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11884, d149506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11885 q = 1) (hb : d146837 q = 1) : d149507 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11885, d149507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11885, d149507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11886 q = 1) (hb : d146837 q = 1) : d149508 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11886, d149508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11886, d149508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27980 (p : Pattern) (ha : d11892 p = 1) (hb : d146837 p = 1) : d149514 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11887 q = 1) (hb : d146837 q = 1) : d149509 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11887, d149509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27979 q ha hb
    | true =>
      simp only [d11887, d149509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11888 q = 1) (hb : d146837 q = 1) : d149510 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11888, d149510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11888, d149510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11889 q = 1) (hb : d146837 q = 1) : d149511 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11889, d149511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11889, d149511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11890 q = 1) (hb : d146837 q = 1) : d149512 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11890, d149512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11890, d149512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11891 q = 1) (hb : d146837 q = 1) : d149513 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11891, d149513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11891, d149513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11892 q = 1) (hb : d146837 q = 1) : d149514 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11892, d149514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11892, d149514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27981 (p : Pattern) (ha : d11681 p = 1) (hb : d146837 p = 1) : d149368 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11647 q = 1) (hb : d146837 q = 1) : d149334 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27966 q ha hb
    | true =>
      simp only [d11647, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11648 q = 1) (hb : d146837 q = 1) : d149335 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11651 q = 1) (hb : d146837 q = 1) : d149338 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27967 q ha hb
    | true =>
      simp only [d11651, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11652 q = 1) (hb : d146837 q = 1) : d149339 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11653 q = 1) (hb : d146837 q = 1) : d149340 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11653, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11654 q = 1) (hb : d146837 q = 1) : d149341 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11654, d149341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11654, d149341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11680 q = 1) (hb : d146837 q = 1) : d149367 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11680, d149367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11680, d149367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11681 q = 1) (hb : d146837 q = 1) : d149368 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11681, d149368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11681, d149368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27982 (p : Pattern) (ha : d11683 p = 1) (hb : d146837 p = 1) : d149370 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11651 q = 1) (hb : d146837 q = 1) : d149338 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27967 q ha hb
    | true =>
      simp only [d11651, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11652 q = 1) (hb : d146837 q = 1) : d149339 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11657 q = 1) (hb : d146837 q = 1) : d149344 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11657, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11657, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11658 q = 1) (hb : d146837 q = 1) : d149345 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11658, d149345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11658, d149345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11682 q = 1) (hb : d146837 q = 1) : d149369 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11682, d149369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11682, d149369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11683 q = 1) (hb : d146837 q = 1) : d149370 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11683, d149370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11683, d149370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27983 (p : Pattern) (ha : d11690 p = 1) (hb : d146837 p = 1) : d149377 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11647 q = 1) (hb : d146837 q = 1) : d149334 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27966 q ha hb
    | true =>
      simp only [d11647, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11648 q = 1) (hb : d146837 q = 1) : d149335 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11651 q = 1) (hb : d146837 q = 1) : d149338 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27967 q ha hb
    | true =>
      simp only [d11651, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11652 q = 1) (hb : d146837 q = 1) : d149339 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11653 q = 1) (hb : d146837 q = 1) : d149340 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11653, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11688 q = 1) (hb : d146837 q = 1) : d149375 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11688, d149375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11688, d149375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11689 q = 1) (hb : d146837 q = 1) : d149376 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11689, d149376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11689, d149376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11690 q = 1) (hb : d146837 q = 1) : d149377 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11690, d149377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11690, d149377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27984 (p : Pattern) (ha : d11693 p = 1) (hb : d146837 p = 1) : d149380 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11651 q = 1) (hb : d146837 q = 1) : d149338 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27967 q ha hb
    | true =>
      simp only [d11651, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11652 q = 1) (hb : d146837 q = 1) : d149339 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11657 q = 1) (hb : d146837 q = 1) : d149344 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11657, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11657, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11691 q = 1) (hb : d146837 q = 1) : d149378 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11691, d149378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11691, d149378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11692 q = 1) (hb : d146837 q = 1) : d149379 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11692, d149379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11692, d149379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11693 q = 1) (hb : d146837 q = 1) : d149380 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11693, d149380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11693, d149380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27985 (p : Pattern) (ha : d1664 p = 1) (hb : d116750 p = 1) : d22312 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1663 q = 1) : d1663 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1538 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1664 q = 1) (hb : d116750 q = 1) : d22312 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1664, d116750, d22312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1664, d116750, d22312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro27986 (p : Pattern) (ha : d1670 p = 1) (hb : d146836 p = 1) : d149384 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1665 q = 1) (hb : d116750 q = 1) : d22313 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1665, d22313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27985 q ha hb
    | true =>
      simp only [d1665, d22313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1666 q = 1) (hb : d116750 q = 1) : d22314 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1666, d22314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1666, d22314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1667 q = 1) (hb : d116750 q = 1) : d22315 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1667, d22315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1667, d22315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1668 q = 1) (hb : d116750 q = 1) : d22316 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1668, d22316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1668, d22316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1555 q = 1) (hb : d116750 q = 1) : d10036 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d10036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20002 q ha hb
    | true =>
      simp only [d1555, d10036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1556 q = 1) (hb : d116750 q = 1) : d10038 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d10038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1556, d10038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1557 q = 1) (hb : d116750 q = 1) : d16859 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1557, d16859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1557, d16859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1558 q = 1) (hb : d116750 q = 1) : d16860 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1558, d16860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1558, d16860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1669 q = 1) (hb : d116750 q = 1) : d22317 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1669, d22317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1669, d22317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d1574 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d1670 q = 1) (hb : d146836 q = 1) : d149384 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d1670, d146836, d149384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1670, d146836, d149384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro27987 (p : Pattern) (ha : d11702 p = 1) (hb : d146837 p = 1) : d149390 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11697 q = 1) (hb : d146837 q = 1) : d149385 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11697, d146837, d149385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27986 q ha hb
    | true =>
      simp only [d11697, d146837, d149385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11698 q = 1) (hb : d146837 q = 1) : d149386 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11698, d149386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11698, d149386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11699 q = 1) (hb : d146837 q = 1) : d149387 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11699, d149387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11699, d149387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11637 q = 1) (hb : d146837 q = 1) : d149323 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11637, d146837, d149323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27964 q ha hb
    | true =>
      simp only [d11637, d146837, d149323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11638 q = 1) (hb : d146837 q = 1) : d149324 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11638, d149324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11638, d149324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11639 q = 1) (hb : d146837 q = 1) : d149325 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11639, d149325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11639, d149325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11700 q = 1) (hb : d146837 q = 1) : d149388 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11700, d149388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11700, d149388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11640 q = 1) (hb : d146837 q = 1) : d149327 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11640, d146837, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27965 q ha hb
    | true =>
      simp only [d11640, d146837, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d11641 q = 1) (hb : d146837 q = 1) : d149328 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11641, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11641, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11642 q = 1) (hb : d146837 q = 1) : d149329 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11642, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11642, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11643 q = 1) (hb : d146837 q = 1) : d149330 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11643, d149330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11643, d149330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11701 q = 1) (hb : d146837 q = 1) : d149389 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11701, d149389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11701, d149389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11702 q = 1) (hb : d146837 q = 1) : d149390 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11702, d149390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11702, d149390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro27988 (p : Pattern) (ha : d11708 p = 1) (hb : d146837 p = 1) : d149396 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11703 q = 1) (hb : d146837 q = 1) : d149391 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11703, d149391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27987 q ha hb
    | true =>
      simp only [d11703, d149391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11704 q = 1) (hb : d146837 q = 1) : d149392 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11704, d149392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11704, d149392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11647 q = 1) (hb : d146837 q = 1) : d149334 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27966 q ha hb
    | true =>
      simp only [d11647, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11648 q = 1) (hb : d146837 q = 1) : d149335 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11705 q = 1) (hb : d146837 q = 1) : d149393 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11705, d149393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11705, d149393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11706 q = 1) (hb : d146837 q = 1) : d149394 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11706, d149394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11706, d149394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11707 q = 1) (hb : d146837 q = 1) : d149395 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11707, d149395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11707, d149395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11708 q = 1) (hb : d146837 q = 1) : d149396 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11708, d149396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11708, d149396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27989 (p : Pattern) (ha : d5635 p = 1) (hb : d146836 p = 1) : d149326 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1570 q = 1) (hb : d116750 q = 1) : d22220 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d22220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19986 q ha hb
    | true =>
      simp only [d1570, d22220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1571 q = 1) (hb : d116750 q = 1) : d22221 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d22221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1571, d22221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1572 q = 1) (hb : d116750 q = 1) : d22222 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1572, d22222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1572, d22222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1573 q = 1) (hb : d116750 q = 1) : d22223 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1573, d22223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1573, d22223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1582 q = 1) (hb : d116750 q = 1) : d22233 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d22233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19973 q ha hb
    | true =>
      simp only [d1582, d22233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1583 q = 1) (hb : d116750 q = 1) : d22234 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d22234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1583, d22234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1584 q = 1) (hb : d116750 q = 1) : d22235 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1584, d22235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1584, d22235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1585 q = 1) (hb : d116750 q = 1) : d22236 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1585, d22236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1585, d22236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1586 q = 1) (hb : d116750 q = 1) : d22237 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1586, d22237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1586, d22237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d5634 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d5635 q = 1) (hb : d146836 q = 1) : d149326 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5635, d146836, d149326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5635, d146836, d149326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro27990 (p : Pattern) (ha : d11741 p = 1) (hb : d146837 p = 1) : d149333 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11637 q = 1) (hb : d146837 q = 1) : d149323 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11637, d146837, d149323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27964 q ha hb
    | true =>
      simp only [d11637, d146837, d149323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11638 q = 1) (hb : d146837 q = 1) : d149324 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11638, d149324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11638, d149324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11639 q = 1) (hb : d146837 q = 1) : d149325 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11639, d149325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11639, d149325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11640 q = 1) (hb : d146837 q = 1) : d149327 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11640, d146837, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27965 q ha hb
    | true =>
      simp only [d11640, d146837, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d11641 q = 1) (hb : d146837 q = 1) : d149328 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11641, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11641, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11642 q = 1) (hb : d146837 q = 1) : d149329 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11642, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11642, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11643 q = 1) (hb : d146837 q = 1) : d149330 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11643, d149330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11643, d149330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11736 q = 1) (hb : d146837 q = 1) : d149327 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11736, d146837, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27989 q ha hb
    | true =>
      simp only [d11736, d146837, d149327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d11737 q = 1) (hb : d146837 q = 1) : d149328 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11737, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11737, d149328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11738 q = 1) (hb : d146837 q = 1) : d149329 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11738, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11738, d149329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11739 q = 1) (hb : d146837 q = 1) : d149331 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11739, d149331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d11739, d149331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d11740 q = 1) (hb : d146837 q = 1) : d149332 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11740, d149332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11740, d149332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d11741 q = 1) (hb : d146837 q = 1) : d149333 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11741, d149333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11741, d149333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro27991 (p : Pattern) (ha : d11747 p = 1) (hb : d146837 p = 1) : d149402 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11742 q = 1) (hb : d146837 q = 1) : d149334 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11742, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27990 q ha hb
    | true =>
      simp only [d11742, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11743 q = 1) (hb : d146837 q = 1) : d149335 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11743, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11743, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11744 q = 1) (hb : d146837 q = 1) : d149399 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11744, d149399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11744, d149399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11745 q = 1) (hb : d146837 q = 1) : d149400 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11745, d149400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11745, d149400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11746 q = 1) (hb : d146837 q = 1) : d149401 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11746, d149401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11746, d149401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11747 q = 1) (hb : d146837 q = 1) : d149402 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11747, d149402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11747, d149402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27992 (p : Pattern) (ha : d108984 p = 1) (hb : d146837 p = 1) : d149408 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11684 q = 1) (hb : d146837 q = 1) : d149371 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11684, d149371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27981 q ha hb
    | true =>
      simp only [d11684, d149371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27982 q ha hb
  have h2 (q : Pattern) (ha : d11685 q = 1) (hb : d146837 q = 1) : d149372 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11685, d149372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11685, d149372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11686 q = 1) (hb : d146837 q = 1) : d149373 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11686, d149373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11686, d149373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11687 q = 1) (hb : d146837 q = 1) : d149374 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11687, d149374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11687, d149374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11694 q = 1) (hb : d146837 q = 1) : d149381 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11694, d149381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27983 q ha hb
    | true =>
      simp only [d11694, d149381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27984 q ha hb
  have h6 (q : Pattern) (ha : d11695 q = 1) (hb : d146837 q = 1) : d149382 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11695, d149382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11695, d149382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11696 q = 1) (hb : d146837 q = 1) : d149383 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11696, d149383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11696, d149383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11709 q = 1) (hb : d146837 q = 1) : d149397 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11709, d149397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27988 q ha hb
    | true =>
      simp only [d11709, d149397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27968 q ha hb
  have h9 (q : Pattern) (ha : d108980 q = 1) (hb : d146837 q = 1) : d149398 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108980, d149398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108980, d149398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11748 q = 1) (hb : d146837 q = 1) : d149403 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11748, d149403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27991 q ha hb
    | true =>
      simp only [d11748, d149403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11749 q = 1) (hb : d146837 q = 1) : d149404 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11749, d149404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11749, d149404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d108981 q = 1) (hb : d146837 q = 1) : d149405 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108981, d149405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108981, d149405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108982 q = 1) (hb : d146837 q = 1) : d149406 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108982, d149406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108982, d149406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108983 q = 1) (hb : d146837 q = 1) : d149407 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108983, d149407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108983, d149407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108984 q = 1) (hb : d146837 q = 1) : d149408 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108984, d149408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108984, d149408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro27993 (p : Pattern) (ha : d11754 p = 1) (hb : d146837 p = 1) : d149409 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11647 q = 1) (hb : d146837 q = 1) : d149334 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27966 q ha hb
    | true =>
      simp only [d11647, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11648 q = 1) (hb : d146837 q = 1) : d149335 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11651 q = 1) (hb : d146837 q = 1) : d149338 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27967 q ha hb
    | true =>
      simp only [d11651, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11652 q = 1) (hb : d146837 q = 1) : d149339 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11653 q = 1) (hb : d146837 q = 1) : d149340 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11653, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11654 q = 1) (hb : d146837 q = 1) : d149341 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11654, d149341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11654, d149341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11680 q = 1) (hb : d146837 q = 1) : d149367 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11680, d149367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11680, d149367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11754 q = 1) (hb : d146837 q = 1) : d149409 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11754, d149409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11754, d149409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27994 (p : Pattern) (ha : d11755 p = 1) (hb : d146837 p = 1) : d149410 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11651 q = 1) (hb : d146837 q = 1) : d149338 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27967 q ha hb
    | true =>
      simp only [d11651, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11652 q = 1) (hb : d146837 q = 1) : d149339 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11657 q = 1) (hb : d146837 q = 1) : d149344 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11657, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11657, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11658 q = 1) (hb : d146837 q = 1) : d149345 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11658, d149345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11658, d149345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11682 q = 1) (hb : d146837 q = 1) : d149369 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11682, d149369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11682, d149369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11755 q = 1) (hb : d146837 q = 1) : d149410 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11755, d149410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11755, d149410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27995 (p : Pattern) (ha : d11760 p = 1) (hb : d146837 p = 1) : d149415 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11647 q = 1) (hb : d146837 q = 1) : d149334 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27966 q ha hb
    | true =>
      simp only [d11647, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11648 q = 1) (hb : d146837 q = 1) : d149335 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11651 q = 1) (hb : d146837 q = 1) : d149338 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27967 q ha hb
    | true =>
      simp only [d11651, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11652 q = 1) (hb : d146837 q = 1) : d149339 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11653 q = 1) (hb : d146837 q = 1) : d149340 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11653, d149340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11688 q = 1) (hb : d146837 q = 1) : d149375 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11688, d149375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11688, d149375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11689 q = 1) (hb : d146837 q = 1) : d149376 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11689, d149376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11689, d149376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11760 q = 1) (hb : d146837 q = 1) : d149415 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11760, d149415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11760, d149415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27996 (p : Pattern) (ha : d11761 p = 1) (hb : d146837 p = 1) : d149416 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11651 q = 1) (hb : d146837 q = 1) : d149338 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27967 q ha hb
    | true =>
      simp only [d11651, d149338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11652 q = 1) (hb : d146837 q = 1) : d149339 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d149339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11657 q = 1) (hb : d146837 q = 1) : d149344 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11657, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11657, d149344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11691 q = 1) (hb : d146837 q = 1) : d149378 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11691, d149378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11691, d149378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11692 q = 1) (hb : d146837 q = 1) : d149379 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11692, d149379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11692, d149379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11761 q = 1) (hb : d146837 q = 1) : d149416 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11761, d149416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11761, d149416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27997 (p : Pattern) (ha : d11765 p = 1) (hb : d146837 p = 1) : d149420 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11703 q = 1) (hb : d146837 q = 1) : d149391 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11703, d149391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27987 q ha hb
    | true =>
      simp only [d11703, d149391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11704 q = 1) (hb : d146837 q = 1) : d149392 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11704, d149392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11704, d149392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11647 q = 1) (hb : d146837 q = 1) : d149334 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27966 q ha hb
    | true =>
      simp only [d11647, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11648 q = 1) (hb : d146837 q = 1) : d149335 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11705 q = 1) (hb : d146837 q = 1) : d149393 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11705, d149393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11705, d149393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11706 q = 1) (hb : d146837 q = 1) : d149394 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11706, d149394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11706, d149394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11707 q = 1) (hb : d146837 q = 1) : d149395 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11707, d149395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11707, d149395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11765 q = 1) (hb : d146837 q = 1) : d149420 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11765, d149420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11765, d149420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27998 (p : Pattern) (ha : d11771 p = 1) (hb : d146837 p = 1) : d149423 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11742 q = 1) (hb : d146837 q = 1) : d149334 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11742, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27990 q ha hb
    | true =>
      simp only [d11742, d149334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11743 q = 1) (hb : d146837 q = 1) : d149335 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11743, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11743, d149335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11744 q = 1) (hb : d146837 q = 1) : d149399 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11744, d149399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11744, d149399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11745 q = 1) (hb : d146837 q = 1) : d149400 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11745, d149400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11745, d149400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11746 q = 1) (hb : d146837 q = 1) : d149401 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11746, d149401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11746, d149401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11771 q = 1) (hb : d146837 q = 1) : d149423 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11771, d149423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11771, d149423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27999 (p : Pattern) (ha : d108989 p = 1) (hb : d146837 p = 1) : d149429 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11684 q = 1) (hb : d146837 q = 1) : d149371 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11684, d149371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27981 q ha hb
    | true =>
      simp only [d11684, d149371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27982 q ha hb
  have h2 (q : Pattern) (ha : d11685 q = 1) (hb : d146837 q = 1) : d149372 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11685, d149372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11685, d149372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11686 q = 1) (hb : d146837 q = 1) : d149373 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11686, d149373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11686, d149373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11687 q = 1) (hb : d146837 q = 1) : d149374 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11687, d149374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11687, d149374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11694 q = 1) (hb : d146837 q = 1) : d149381 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11694, d149381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27983 q ha hb
    | true =>
      simp only [d11694, d149381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27984 q ha hb
  have h6 (q : Pattern) (ha : d11695 q = 1) (hb : d146837 q = 1) : d149382 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11695, d149382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11695, d149382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11696 q = 1) (hb : d146837 q = 1) : d149383 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11696, d149383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11696, d149383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11709 q = 1) (hb : d146837 q = 1) : d149397 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11709, d149397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27988 q ha hb
    | true =>
      simp only [d11709, d149397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27968 q ha hb
  have h9 (q : Pattern) (ha : d108980 q = 1) (hb : d146837 q = 1) : d149398 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108980, d149398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108980, d149398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11748 q = 1) (hb : d146837 q = 1) : d149403 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11748, d149403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27991 q ha hb
    | true =>
      simp only [d11748, d149403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11749 q = 1) (hb : d146837 q = 1) : d149404 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11749, d149404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11749, d149404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d108981 q = 1) (hb : d146837 q = 1) : d149405 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108981, d149405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108981, d149405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108982 q = 1) (hb : d146837 q = 1) : d149406 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108982, d149406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108982, d149406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108983 q = 1) (hb : d146837 q = 1) : d149407 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108983, d149407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108983, d149407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d11756 q = 1) (hb : d146837 q = 1) : d149411 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11756, d149411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27993 q ha hb
    | true =>
      simp only [d11756, d149411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27994 q ha hb
  have h16 (q : Pattern) (ha : d11757 q = 1) (hb : d146837 q = 1) : d149412 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11757, d149412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11757, d149412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d11758 q = 1) (hb : d146837 q = 1) : d149413 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11758, d149413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d11758, d149413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d11759 q = 1) (hb : d146837 q = 1) : d149414 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11759, d149414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11759, d149414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d11762 q = 1) (hb : d146837 q = 1) : d149417 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11762, d149417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27995 q ha hb
    | true =>
      simp only [d11762, d149417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27996 q ha hb
  have h20 (q : Pattern) (ha : d11763 q = 1) (hb : d146837 q = 1) : d149418 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11763, d149418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11763, d149418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d11764 q = 1) (hb : d146837 q = 1) : d149419 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11764, d149419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d11764, d149419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d11766 q = 1) (hb : d146837 q = 1) : d149421 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11766, d149421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27997 q ha hb
    | true =>
      simp only [d11766, d149421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27971 q ha hb
  have h23 (q : Pattern) (ha : d108985 q = 1) (hb : d146837 q = 1) : d149422 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108985, d149422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d108985, d149422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d11772 q = 1) (hb : d146837 q = 1) : d149424 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11772, d149424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27998 q ha hb
    | true =>
      simp only [d11772, d149424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d11773 q = 1) (hb : d146837 q = 1) : d149425 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11773, d149425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d11773, d149425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d108986 q = 1) (hb : d146837 q = 1) : d149426 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108986, d149426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d108986, d149426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d108987 q = 1) (hb : d146837 q = 1) : d149427 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108987, d149427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108987, d149427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d108988 q = 1) (hb : d146837 q = 1) : d149428 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108988, d149428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d108988, d149428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d108989 q = 1) (hb : d146837 q = 1) : d149429 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108989, d149429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108989, d149429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
end NetHack.Soko22Hazard87
