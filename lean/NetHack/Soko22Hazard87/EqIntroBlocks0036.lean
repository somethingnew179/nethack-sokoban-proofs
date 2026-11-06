import NetHack.Soko22Hazard87.EqIntroBlocks0035
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro9000 (p : Pattern) (selected : d117591 p = 0) : d119211 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117582 q = 0) : d119202 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117582, d119202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8998 q selected
    | true =>
      simp only [d117582, d119202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117583 q = 0) : d119203 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117583, d119203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117583, d119203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117588 q = 0) : d119208 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117588, d119208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117588, d119208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117589 q = 0) : d119209 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117589, d119209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117589, d119209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117590 q = 0) : d119210 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117590, d119210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117590, d119210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117591 q = 0) : d119211 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117591, d119211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117591, d119211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9001 (p : Pattern) (selected : d117597 p = 0) : d119278 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117477 q = 0) : d119198 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117477, d119198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8973 q selected
    | true =>
      simp only [d117477, d119198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117478 q = 0) : d119199 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117478, d119199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117478, d119199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117594 q = 0) : d119275 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117594, d119275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117594, d119275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117595 q = 0) : d119276 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117595, d119276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117595, d119276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117596 q = 0) : d119277 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117596, d119277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117596, d119277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117597 q = 0) : d119278 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117597, d119278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117597, d119278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9002 (p : Pattern) (selected : d117603 p = 0) : d119284 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117514 q = 0) : d119235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117514, d119235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8981 q selected
    | true =>
      simp only [d117514, d119235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8982 q selected
  have h2 (q : Pattern) (selected : d117515 q = 0) : d119236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117515, d119236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117515, d119236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117516 q = 0) : d119237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117516, d119237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117516, d119237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117517 q = 0) : d119238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117517, d119238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117517, d119238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117524 q = 0) : d119245 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117524, d119245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8983 q selected
    | true =>
      simp only [d117524, d119245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8984 q selected
  have h6 (q : Pattern) (selected : d117525 q = 0) : d119246 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117525, d119246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117525, d119246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117526 q = 0) : d119247 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117526, d119247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117526, d119247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117552 q = 0) : d119273 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117552, d119273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8990 q selected
    | true =>
      simp only [d117552, d119273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8975 q selected
  have h9 (q : Pattern) (selected : d117592 q = 0) : d119212 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117592, d119212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8999 q selected
    | true =>
      simp only [d117592, d119212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9000 q selected
  have h10 (q : Pattern) (selected : d117593 q = 0) : d119274 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117593, d119274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117593, d119274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d117598 q = 0) : d119279 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117598, d119279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9001 q selected
    | true =>
      simp only [d117598, d119279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d117599 q = 0) : d119280 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117599, d119280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d117599, d119280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d117600 q = 0) : d119281 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117600, d119281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d117600, d119281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d117601 q = 0) : d119282 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117601, d119282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117601, d119282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d117602 q = 0) : d119283 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117602, d119283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117602, d119283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d117603 q = 0) : d119284 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117603, d119284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117603, d119284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro9003 (p : Pattern) (selected : d117604 p = 0) : d119285 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117477 q = 0) : d119198 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117477, d119198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8973 q selected
    | true =>
      simp only [d117477, d119198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117478 q = 0) : d119199 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117478, d119199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117478, d119199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117481 q = 0) : d119202 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117481, d119202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8974 q selected
    | true =>
      simp only [d117481, d119202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117482 q = 0) : d119203 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117482, d119203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117482, d119203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117483 q = 0) : d119204 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117483, d119204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117483, d119204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117484 q = 0) : d119205 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117484, d119205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117484, d119205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117510 q = 0) : d119231 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117510, d119231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117510, d119231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117604 q = 0) : d119285 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117604, d119285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117604, d119285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9004 (p : Pattern) (selected : d117605 p = 0) : d119286 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117481 q = 0) : d119202 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117481, d119202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8974 q selected
    | true =>
      simp only [d117481, d119202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117482 q = 0) : d119203 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117482, d119203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117482, d119203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117487 q = 0) : d119208 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117487, d119208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117487, d119208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117488 q = 0) : d119209 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117488, d119209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117488, d119209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117512 q = 0) : d119233 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117512, d119233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117512, d119233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117605 q = 0) : d119286 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117605, d119286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117605, d119286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9005 (p : Pattern) (selected : d117610 p = 0) : d119291 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117477 q = 0) : d119198 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117477, d119198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8973 q selected
    | true =>
      simp only [d117477, d119198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117478 q = 0) : d119199 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117478, d119199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117478, d119199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117481 q = 0) : d119202 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117481, d119202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8974 q selected
    | true =>
      simp only [d117481, d119202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117482 q = 0) : d119203 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117482, d119203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117482, d119203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117483 q = 0) : d119204 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117483, d119204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117483, d119204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117518 q = 0) : d119239 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117518, d119239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117518, d119239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117519 q = 0) : d119240 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117519, d119240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117519, d119240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117610 q = 0) : d119291 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117610, d119291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117610, d119291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9006 (p : Pattern) (selected : d117611 p = 0) : d119292 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117481 q = 0) : d119202 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117481, d119202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8974 q selected
    | true =>
      simp only [d117481, d119202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117482 q = 0) : d119203 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117482, d119203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117482, d119203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117487 q = 0) : d119208 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117487, d119208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117487, d119208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117521 q = 0) : d119242 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117521, d119242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117521, d119242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117522 q = 0) : d119243 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117522, d119243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117522, d119243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117611 q = 0) : d119292 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117611, d119292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117611, d119292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9007 (p : Pattern) (selected : d117615 p = 0) : d119296 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117546 q = 0) : d119267 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117546, d119267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8989 q selected
    | true =>
      simp only [d117546, d119267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117547 q = 0) : d119268 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117547, d119268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117547, d119268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117477 q = 0) : d119198 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117477, d119198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8973 q selected
    | true =>
      simp only [d117477, d119198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117478 q = 0) : d119199 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117478, d119199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117478, d119199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117548 q = 0) : d119269 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117548, d119269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117548, d119269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117549 q = 0) : d119270 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117549, d119270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117549, d119270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117550 q = 0) : d119271 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117550, d119271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117550, d119271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117615 q = 0) : d119296 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117615, d119296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117615, d119296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9008 (p : Pattern) (selected : d117617 p = 0) : d119220 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117578 q = 0) : d119198 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117578, d119198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8997 q selected
    | true =>
      simp only [d117578, d119198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117579 q = 0) : d119199 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117579, d119199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117579, d119199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117582 q = 0) : d119202 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117582, d119202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8998 q selected
    | true =>
      simp only [d117582, d119202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117583 q = 0) : d119203 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117583, d119203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117583, d119203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117584 q = 0) : d119204 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117584, d119204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117584, d119204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117585 q = 0) : d119205 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117585, d119205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117585, d119205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117586 q = 0) : d119206 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117586, d119206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117586, d119206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117617 q = 0) : d119220 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117617, d119220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117617, d119220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9009 (p : Pattern) (selected : d117618 p = 0) : d119221 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117582 q = 0) : d119202 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117582, d119202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8998 q selected
    | true =>
      simp only [d117582, d119202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117583 q = 0) : d119203 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117583, d119203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117583, d119203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117588 q = 0) : d119208 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117588, d119208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117588, d119208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117589 q = 0) : d119209 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117589, d119209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117589, d119209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117590 q = 0) : d119210 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117590, d119210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117590, d119210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117618 q = 0) : d119221 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117618, d119221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117618, d119221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9010 (p : Pattern) (selected : d117621 p = 0) : d119299 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117477 q = 0) : d119198 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117477, d119198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8973 q selected
    | true =>
      simp only [d117477, d119198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117478 q = 0) : d119199 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117478, d119199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117478, d119199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117594 q = 0) : d119275 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117594, d119275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117594, d119275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117595 q = 0) : d119276 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117595, d119276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117595, d119276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117596 q = 0) : d119277 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117596, d119277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117596, d119277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117621 q = 0) : d119299 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117621, d119299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117621, d119299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9011 (p : Pattern) (selected : d117627 p = 0) : d119305 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117514 q = 0) : d119235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117514, d119235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8981 q selected
    | true =>
      simp only [d117514, d119235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8982 q selected
  have h2 (q : Pattern) (selected : d117515 q = 0) : d119236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117515, d119236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117515, d119236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117516 q = 0) : d119237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117516, d119237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117516, d119237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117517 q = 0) : d119238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117517, d119238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117517, d119238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117524 q = 0) : d119245 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117524, d119245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8983 q selected
    | true =>
      simp only [d117524, d119245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8984 q selected
  have h6 (q : Pattern) (selected : d117525 q = 0) : d119246 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117525, d119246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117525, d119246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117526 q = 0) : d119247 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117526, d119247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117526, d119247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117552 q = 0) : d119273 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117552, d119273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8990 q selected
    | true =>
      simp only [d117552, d119273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8975 q selected
  have h9 (q : Pattern) (selected : d117592 q = 0) : d119212 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117592, d119212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8999 q selected
    | true =>
      simp only [d117592, d119212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9000 q selected
  have h10 (q : Pattern) (selected : d117593 q = 0) : d119274 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117593, d119274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117593, d119274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d117598 q = 0) : d119279 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117598, d119279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9001 q selected
    | true =>
      simp only [d117598, d119279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d117599 q = 0) : d119280 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117599, d119280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d117599, d119280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d117600 q = 0) : d119281 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117600, d119281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d117600, d119281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d117601 q = 0) : d119282 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117601, d119282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117601, d119282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d117602 q = 0) : d119283 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117602, d119283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117602, d119283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d117606 q = 0) : d119287 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117606, d119287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9003 q selected
    | true =>
      simp only [d117606, d119287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9004 q selected
  have h17 (q : Pattern) (selected : d117607 q = 0) : d119288 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117607, d119288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117607, d119288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d117608 q = 0) : d119289 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117608, d119289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d117608, d119289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d117609 q = 0) : d119290 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117609, d119290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117609, d119290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d117612 q = 0) : d119293 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117612, d119293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9005 q selected
    | true =>
      simp only [d117612, d119293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9006 q selected
  have h21 (q : Pattern) (selected : d117613 q = 0) : d119294 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117613, d119294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117613, d119294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d117614 q = 0) : d119295 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117614, d119295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d117614, d119295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d117616 q = 0) : d119297 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117616, d119297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9007 q selected
    | true =>
      simp only [d117616, d119297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8978 q selected
  have h24 (q : Pattern) (selected : d117619 q = 0) : d119222 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117619, d119222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9008 q selected
    | true =>
      simp only [d117619, d119222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9009 q selected
  have h25 (q : Pattern) (selected : d117620 q = 0) : d119298 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117620, d119298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d117620, d119298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d117622 q = 0) : d119300 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117622, d119300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9010 q selected
    | true =>
      simp only [d117622, d119300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d117623 q = 0) : d119301 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117623, d119301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d117623, d119301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d117624 q = 0) : d119302 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117624, d119302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d117624, d119302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d117625 q = 0) : d119303 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117625, d119303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d117625, d119303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d117626 q = 0) : d119304 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117626, d119304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d117626, d119304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d117627 q = 0) : d119305 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117627, d119305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d117627, d119305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro9012 (p : Pattern) (selected : d117634 p = 0) : d119312 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117491 q = 0) : d119212 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117491, d119212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8975 q selected
    | true =>
      simp only [d117491, d119212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8976 q selected
  have h2 (q : Pattern) (selected : d117492 q = 0) : d119213 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117492, d119213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117492, d119213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117493 q = 0) : d119214 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117493, d119214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117493, d119214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117494 q = 0) : d119215 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117494, d119215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117494, d119215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117495 q = 0) : d119216 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117495, d119216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117495, d119216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117629 q = 0) : d119307 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117629, d119307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8976 q selected
    | true =>
      simp only [d117629, d119307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117630 q = 0) : d119308 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117630, d119308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117630, d119308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117631 q = 0) : d119309 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117631, d119309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117631, d119309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117632 q = 0) : d119310 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117632, d119310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117632, d119310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117633 q = 0) : d119311 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117633, d119311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117633, d119311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d117634 q = 0) : d119312 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117634, d119312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117634, d119312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro9013 (p : Pattern) (selected : d117640 p = 0) : d119318 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117629 q = 0) : d119307 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117629, d119307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8976 q selected
    | true =>
      simp only [d117629, d119307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117630 q = 0) : d119308 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117630, d119308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117630, d119308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117631 q = 0) : d119309 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117631, d119309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117631, d119309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117632 q = 0) : d119310 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117632, d119310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117632, d119310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117633 q = 0) : d119311 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117633, d119311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117633, d119311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117635 q = 0) : d119313 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117635, d119313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8979 q selected
    | true =>
      simp only [d117635, d119313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117636 q = 0) : d119314 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117636, d119314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117636, d119314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117637 q = 0) : d119315 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117637, d119315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117637, d119315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117638 q = 0) : d119316 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117638, d119316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117638, d119316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117639 q = 0) : d119317 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117639, d119317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117639, d119317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d117640 q = 0) : d119318 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117640, d119318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117640, d119318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro9014 (p : Pattern) (selected : d117647 p = 0) : d119325 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117616 q = 0) : d119297 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117616, d119297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9007 q selected
    | true =>
      simp only [d117616, d119297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8978 q selected
  have h2 (q : Pattern) (selected : d117619 q = 0) : d119222 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117619, d119222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9008 q selected
    | true =>
      simp only [d117619, d119222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9009 q selected
  have h3 (q : Pattern) (selected : d117620 q = 0) : d119298 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117620, d119298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117620, d119298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117622 q = 0) : d119300 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117622, d119300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9010 q selected
    | true =>
      simp only [d117622, d119300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117623 q = 0) : d119301 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117623, d119301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117623, d119301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117624 q = 0) : d119302 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117624, d119302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117624, d119302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117645 q = 0) : d119323 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117645, d119323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117645, d119323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117646 q = 0) : d119324 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117646, d119324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117646, d119324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d117647 q = 0) : d119325 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117647, d119325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117647, d119325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro9015 (p : Pattern) (selected : d117649 p = 0) : d119327 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117635 q = 0) : d119313 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117635, d119313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8979 q selected
    | true =>
      simp only [d117635, d119313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117636 q = 0) : d119314 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117636, d119314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117636, d119314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117637 q = 0) : d119315 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117637, d119315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117637, d119315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117638 q = 0) : d119316 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117638, d119316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117638, d119316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117639 q = 0) : d119317 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117639, d119317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117639, d119317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117649 q = 0) : d119327 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117649, d119327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117649, d119327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9016 (p : Pattern) (selected : d117663 p = 0) : d119341 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117655 q = 0) : d119333 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117655, d119333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117655, d119333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8985 q selected
  have h2 (q : Pattern) (selected : d117527 q = 0) : d119248 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117527, d119248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8985 q selected
    | true =>
      simp only [d117527, d119248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117656 q = 0) : d119334 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117656, d119334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117656, d119334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117528 q = 0) : d119249 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117528, d119249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117528, d119249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117657 q = 0) : d119335 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117657, d119335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117657, d119335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117658 q = 0) : d119336 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117658, d119336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117658, d119336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117659 q = 0) : d119337 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117659, d119337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117659, d119337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8967 q selected
  have h8 (q : Pattern) (selected : d117452 q = 0) : d119173 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117452, d119173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8967 q selected
    | true =>
      simp only [d117452, d119173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117660 q = 0) : d119338 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117660, d119338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117660, d119338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117453 q = 0) : d119174 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117453, d119174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117453, d119174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d117661 q = 0) : d119339 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117661, d119339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117661, d119339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d117662 q = 0) : d119340 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117662, d119340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d117662, d119340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d117663 q = 0) : d119341 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117663, d119341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117663, d119341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro9017 (p : Pattern) (selected : d117668 p = 0) : d119346 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117659 q = 0) : d119337 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117659, d119337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117659, d119337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8967 q selected
  have h2 (q : Pattern) (selected : d117452 q = 0) : d119173 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117452, d119173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8967 q selected
    | true =>
      simp only [d117452, d119173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117660 q = 0) : d119338 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117660, d119338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117660, d119338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117453 q = 0) : d119174 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117453, d119174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117453, d119174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117661 q = 0) : d119339 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117661, d119339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117661, d119339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117662 q = 0) : d119340 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117662, d119340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117662, d119340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117664 q = 0) : d119342 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117664, d119342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117664, d119342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8968 q selected
  have h8 (q : Pattern) (selected : d117456 q = 0) : d119177 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117456, d119177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8968 q selected
    | true =>
      simp only [d117456, d119177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117665 q = 0) : d119343 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117665, d119343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117665, d119343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117457 q = 0) : d119178 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117457, d119178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117457, d119178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d117666 q = 0) : d119344 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117666, d119344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117666, d119344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d117667 q = 0) : d119345 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117667, d119345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d117667, d119345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d117668 q = 0) : d119346 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117668, d119346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117668, d119346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro9018 (p : Pattern) (selected : d117676 p = 0) : d119354 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117672 q = 0) : d119350 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117672, d119350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117672, d119350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8987 q selected
  have h2 (q : Pattern) (selected : d117535 q = 0) : d119256 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117535, d119256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8987 q selected
    | true =>
      simp only [d117535, d119256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117673 q = 0) : d119351 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117673, d119351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117673, d119351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117536 q = 0) : d119257 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117536, d119257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117536, d119257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117674 q = 0) : d119352 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117674, d119352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117674, d119352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117675 q = 0) : d119353 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117675, d119353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117675, d119353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117676 q = 0) : d119354 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117676, d119354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117676, d119354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro9019 (p : Pattern) (selected : d117685 p = 0) : d119363 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117664 q = 0) : d119342 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117664, d119342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117664, d119342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8968 q selected
  have h2 (q : Pattern) (selected : d117456 q = 0) : d119177 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117456, d119177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8968 q selected
    | true =>
      simp only [d117456, d119177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117665 q = 0) : d119343 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117665, d119343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117665, d119343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117457 q = 0) : d119178 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117457, d119178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117457, d119178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117666 q = 0) : d119344 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117666, d119344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117666, d119344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117667 q = 0) : d119345 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117667, d119345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117667, d119345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117681 q = 0) : d119359 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117681, d119359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117681, d119359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8970 q selected
  have h8 (q : Pattern) (selected : d117461 q = 0) : d119182 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117461, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8970 q selected
    | true =>
      simp only [d117461, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117682 q = 0) : d119360 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117682, d119360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117682, d119360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117462 q = 0) : d119183 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117462, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117462, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d117683 q = 0) : d119361 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117683, d119361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117683, d119361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d117684 q = 0) : d119362 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117684, d119362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d117684, d119362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d117685 q = 0) : d119363 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117685, d119363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117685, d119363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro9020 (p : Pattern) (selected : d117689 p = 0) : d119367 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117681 q = 0) : d119359 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117681, d119359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117681, d119359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8970 q selected
  have h2 (q : Pattern) (selected : d117461 q = 0) : d119182 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117461, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8970 q selected
    | true =>
      simp only [d117461, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117682 q = 0) : d119360 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117682, d119360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117682, d119360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117462 q = 0) : d119183 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117462, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117462, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117683 q = 0) : d119361 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117683, d119361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117683, d119361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117684 q = 0) : d119362 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117684, d119362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117684, d119362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117689 q = 0) : d119367 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117689, d119367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117689, d119367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro9021 (p : Pattern) (selected : d117695 p = 0) : d119373 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117669 q = 0) : d119347 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117669, d119347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9016 q selected
    | true =>
      simp only [d117669, d119347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9017 q selected
  have h2 (q : Pattern) (selected : d117670 q = 0) : d119348 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117670, d119348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117670, d119348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117671 q = 0) : d119349 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117671, d119349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117671, d119349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117677 q = 0) : d119355 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117677, d119355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9017 q selected
    | true =>
      simp only [d117677, d119355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9018 q selected
  have h5 (q : Pattern) (selected : d117678 q = 0) : d119356 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117678, d119356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117678, d119356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117679 q = 0) : d119357 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117679, d119357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117679, d119357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117680 q = 0) : d119358 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117680, d119358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117680, d119358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117686 q = 0) : d119364 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117686, d119364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9017 q selected
    | true =>
      simp only [d117686, d119364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9019 q selected
  have h9 (q : Pattern) (selected : d117687 q = 0) : d119365 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117687, d119365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117687, d119365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117688 q = 0) : d119366 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117688, d119366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117688, d119366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d117690 q = 0) : d119368 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117690, d119368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9019 q selected
    | true =>
      simp only [d117690, d119368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9020 q selected
  have h12 (q : Pattern) (selected : d117691 q = 0) : d119369 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117691, d119369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117691, d119369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d117692 q = 0) : d119370 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117692, d119370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117692, d119370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d117693 q = 0) : d119371 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117693, d119371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d117693, d119371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d117694 q = 0) : d119372 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117694, d119372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117694, d119372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d117695 q = 0) : d119373 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117695, d119373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d117695, d119373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro9022 (p : Pattern) (selected : d117700 p = 0) : d119378 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117686 q = 0) : d119364 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117686, d119364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9017 q selected
    | true =>
      simp only [d117686, d119364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9019 q selected
  have h2 (q : Pattern) (selected : d117687 q = 0) : d119365 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117687, d119365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117687, d119365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117688 q = 0) : d119366 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117688, d119366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117688, d119366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117690 q = 0) : d119368 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117690, d119368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9019 q selected
    | true =>
      simp only [d117690, d119368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9020 q selected
  have h5 (q : Pattern) (selected : d117691 q = 0) : d119369 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117691, d119369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117691, d119369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117692 q = 0) : d119370 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117692, d119370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117692, d119370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117693 q = 0) : d119371 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117693, d119371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117693, d119371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117698 q = 0) : d119376 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117698, d119376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117698, d119376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117699 q = 0) : d119377 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117699, d119377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117699, d119377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117700 q = 0) : d119378 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117700, d119378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117700, d119378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro9023 (p : Pattern) (selected : d117706 p = 0) : d119384 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117696 q = 0) : d119374 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117696, d119374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9021 q selected
    | true =>
      simp only [d117696, d119374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117697 q = 0) : d119375 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117697, d119375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117697, d119375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117701 q = 0) : d119379 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117701, d119379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9022 q selected
    | true =>
      simp only [d117701, d119379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117702 q = 0) : d119380 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117702, d119380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117702, d119380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117703 q = 0) : d119381 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117703, d119381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117703, d119381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117704 q = 0) : d119382 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117704, d119382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117704, d119382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117705 q = 0) : d119383 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117705, d119383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117705, d119383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117706 q = 0) : d119384 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117706, d119384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117706, d119384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9024 (p : Pattern) (selected : d117708 p = 0) : d119386 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117690 q = 0) : d119368 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117690, d119368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9019 q selected
    | true =>
      simp only [d117690, d119368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9020 q selected
  have h2 (q : Pattern) (selected : d117691 q = 0) : d119369 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117691, d119369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117691, d119369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117692 q = 0) : d119370 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117692, d119370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117692, d119370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117698 q = 0) : d119376 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117698, d119376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117698, d119376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117707 q = 0) : d119385 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117707, d119385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117707, d119385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117708 q = 0) : d119386 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117708, d119386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117708, d119386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9025 (p : Pattern) (selected : d117714 p = 0) : d119392 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117701 q = 0) : d119379 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117701, d119379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9022 q selected
    | true =>
      simp only [d117701, d119379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117702 q = 0) : d119380 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117702, d119380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117702, d119380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117709 q = 0) : d119387 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117709, d119387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9024 q selected
    | true =>
      simp only [d117709, d119387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117710 q = 0) : d119388 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117710, d119388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117710, d119388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117711 q = 0) : d119389 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117711, d119389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117711, d119389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117712 q = 0) : d119390 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117712, d119390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117712, d119390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117713 q = 0) : d119391 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117713, d119391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117713, d119391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117714 q = 0) : d119392 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117714, d119392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117714, d119392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9026 (p : Pattern) (selected : d117724 p = 0) : d119346 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117716 q = 0) : d119337 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117716, d119337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117716, d119337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8991 q selected
  have h2 (q : Pattern) (selected : d117553 q = 0) : d119173 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117553, d119173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8991 q selected
    | true =>
      simp only [d117553, d119173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117717 q = 0) : d119338 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117717, d119338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117717, d119338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117554 q = 0) : d119174 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117554, d119174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117554, d119174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117718 q = 0) : d119339 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117718, d119339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117718, d119339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117719 q = 0) : d119340 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117719, d119340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117719, d119340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117720 q = 0) : d119342 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117720, d119342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117720, d119342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8992 q selected
  have h8 (q : Pattern) (selected : d117557 q = 0) : d119177 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117557, d119177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8992 q selected
    | true =>
      simp only [d117557, d119177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117721 q = 0) : d119343 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117721, d119343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117721, d119343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117558 q = 0) : d119178 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117558, d119178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117558, d119178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d117722 q = 0) : d119344 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117722, d119344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117722, d119344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d117723 q = 0) : d119345 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117723, d119345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d117723, d119345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d117724 q = 0) : d119346 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117724, d119346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117724, d119346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro9027 (p : Pattern) (selected : d117729 p = 0) : d119363 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117720 q = 0) : d119342 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117720, d119342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117720, d119342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8992 q selected
  have h2 (q : Pattern) (selected : d117557 q = 0) : d119177 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117557, d119177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8992 q selected
    | true =>
      simp only [d117557, d119177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117721 q = 0) : d119343 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117721, d119343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117721, d119343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117558 q = 0) : d119178 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117558, d119178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117558, d119178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117722 q = 0) : d119344 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117722, d119344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117722, d119344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117723 q = 0) : d119345 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117723, d119345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117723, d119345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117725 q = 0) : d119359 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117725, d119359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117725, d119359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8994 q selected
  have h8 (q : Pattern) (selected : d117562 q = 0) : d119182 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117562, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8994 q selected
    | true =>
      simp only [d117562, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117726 q = 0) : d119360 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117726, d119360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117726, d119360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117563 q = 0) : d119183 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117563, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117563, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d117727 q = 0) : d119361 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117727, d119361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117727, d119361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d117728 q = 0) : d119362 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117728, d119362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d117728, d119362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d117729 q = 0) : d119363 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117729, d119363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117729, d119363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro9028 (p : Pattern) (selected : d117733 p = 0) : d119367 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117725 q = 0) : d119359 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117725, d119359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117725, d119359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8994 q selected
  have h2 (q : Pattern) (selected : d117562 q = 0) : d119182 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117562, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8994 q selected
    | true =>
      simp only [d117562, d119182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117726 q = 0) : d119360 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117726, d119360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117726, d119360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117563 q = 0) : d119183 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117563, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117563, d119183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117727 q = 0) : d119361 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117727, d119361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117727, d119361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117728 q = 0) : d119362 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117728, d119362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117728, d119362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117733 q = 0) : d119367 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117733, d119367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117733, d119367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro9029 (p : Pattern) (selected : d117740 p = 0) : d119378 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117730 q = 0) : d119364 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117730, d119364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9026 q selected
    | true =>
      simp only [d117730, d119364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9027 q selected
  have h2 (q : Pattern) (selected : d117731 q = 0) : d119365 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117731, d119365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117731, d119365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117732 q = 0) : d119366 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117732, d119366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117732, d119366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117734 q = 0) : d119368 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117734, d119368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9027 q selected
    | true =>
      simp only [d117734, d119368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9028 q selected
  have h5 (q : Pattern) (selected : d117735 q = 0) : d119369 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117735, d119369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117735, d119369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117736 q = 0) : d119370 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117736, d119370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117736, d119370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117737 q = 0) : d119371 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117737, d119371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117737, d119371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117738 q = 0) : d119376 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117738, d119376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117738, d119376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117739 q = 0) : d119377 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117739, d119377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117739, d119377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117740 q = 0) : d119378 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117740, d119378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117740, d119378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro9030 (p : Pattern) (selected : d117744 p = 0) : d119386 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117734 q = 0) : d119368 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117734, d119368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9027 q selected
    | true =>
      simp only [d117734, d119368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9028 q selected
  have h2 (q : Pattern) (selected : d117735 q = 0) : d119369 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117735, d119369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117735, d119369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117736 q = 0) : d119370 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117736, d119370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117736, d119370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117738 q = 0) : d119376 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117738, d119376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117738, d119376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117743 q = 0) : d119385 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117743, d119385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117743, d119385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117744 q = 0) : d119386 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117744, d119386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117744, d119386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9031 (p : Pattern) (selected : d117750 p = 0) : d119392 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117741 q = 0) : d119379 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117741, d119379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9029 q selected
    | true =>
      simp only [d117741, d119379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117742 q = 0) : d119380 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117742, d119380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117742, d119380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117745 q = 0) : d119387 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117745, d119387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9030 q selected
    | true =>
      simp only [d117745, d119387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117746 q = 0) : d119388 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117746, d119388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117746, d119388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117747 q = 0) : d119389 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117747, d119389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117747, d119389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117748 q = 0) : d119390 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117748, d119390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117748, d119390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117749 q = 0) : d119391 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117749, d119391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117749, d119391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117750 q = 0) : d119392 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117750, d119392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117750, d119392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9032 (p : Pattern) (selected : d117754 p = 0) : d119397 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117745 q = 0) : d119387 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117745, d119387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9030 q selected
    | true =>
      simp only [d117745, d119387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117746 q = 0) : d119388 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117746, d119388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117746, d119388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117751 q = 0) : d119394 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117751, d119394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117751, d119394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117752 q = 0) : d119395 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117752, d119395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117752, d119395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117753 q = 0) : d119396 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117753, d119396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117753, d119396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117754 q = 0) : d119397 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117754, d119397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117754, d119397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9033 (p : Pattern) (selected : d117760 p = 0) : d119403 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117701 q = 0) : d119379 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117701, d119379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9022 q selected
    | true =>
      simp only [d117701, d119379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117702 q = 0) : d119380 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117702, d119380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117702, d119380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117757 q = 0) : d119400 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117757, d119400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117757, d119400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117758 q = 0) : d119401 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117758, d119401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117758, d119401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117759 q = 0) : d119402 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117759, d119402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117759, d119402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117760 q = 0) : d119403 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117760, d119403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117760, d119403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9034 (p : Pattern) (selected : d117766 p = 0) : d119409 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117715 q = 0) : d119393 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117715, d119393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9023 q selected
    | true =>
      simp only [d117715, d119393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9025 q selected
  have h2 (q : Pattern) (selected : d117755 q = 0) : d119398 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117755, d119398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9031 q selected
    | true =>
      simp only [d117755, d119398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9032 q selected
  have h3 (q : Pattern) (selected : d117756 q = 0) : d119399 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117756, d119399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117756, d119399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117761 q = 0) : d119404 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117761, d119404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9033 q selected
    | true =>
      simp only [d117761, d119404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117762 q = 0) : d119405 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117762, d119405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117762, d119405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117763 q = 0) : d119406 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117763, d119406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117763, d119406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117764 q = 0) : d119407 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117764, d119407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117764, d119407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117765 q = 0) : d119408 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117765, d119408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117765, d119408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d117766 q = 0) : d119409 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117766, d119409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117766, d119409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro9035 (p : Pattern) (selected : d117771 p = 0) : d119397 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117709 q = 0) : d119387 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117709, d119387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9024 q selected
    | true =>
      simp only [d117709, d119387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117710 q = 0) : d119388 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117710, d119388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117710, d119388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117768 q = 0) : d119394 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117768, d119394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117768, d119394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117769 q = 0) : d119395 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117769, d119395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117769, d119395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117770 q = 0) : d119396 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117770, d119396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117770, d119396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117771 q = 0) : d119397 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117771, d119397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117771, d119397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9036 (p : Pattern) (selected : d117777 p = 0) : d119416 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117772 q = 0) : d119411 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117772, d119411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9035 q selected
    | true =>
      simp only [d117772, d119411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117773 q = 0) : d119412 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117773, d119412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117773, d119412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117774 q = 0) : d119413 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117774, d119413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117774, d119413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117775 q = 0) : d119414 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117775, d119414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117775, d119414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117776 q = 0) : d119415 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117776, d119415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117776, d119415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117777 q = 0) : d119416 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117777, d119416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117777, d119416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9037 (p : Pattern) (selected : d117783 p = 0) : d119422 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117497 q = 0) : d119218 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d117497, d119218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117497, d119218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8977 q selected
  have h2 (q : Pattern) (selected : d117498 q = 0) : d119219 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d117498, d119219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117498, d119219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117507 q = 0) : d119228 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d117507, d119228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8977 q selected
    | true =>
      simp only [d117507, d119228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8980 q selected
  have h4 (q : Pattern) (selected : d117508 q = 0) : d119229 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d117508, d119229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117508, d119229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117509 q = 0) : d119230 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d117509, d119230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117509, d119230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117628 q = 0) : d119306 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d117628, d119306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9002 q selected
    | true =>
      simp only [d117628, d119306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9011 q selected
  have h7 (q : Pattern) (selected : d117641 q = 0) : d119319 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d117641, d119319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9012 q selected
    | true =>
      simp only [d117641, d119319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9013 q selected
  have h8 (q : Pattern) (selected : d117642 q = 0) : d119320 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d117642, d119320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117642, d119320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d117643 q = 0) : d119321 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d117643, d119321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117643, d119321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d117644 q = 0) : d119322 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d117644, d119322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117644, d119322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d117648 q = 0) : d119326 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d117648, d119326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117648, d119326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9014 q selected
  have h12 (q : Pattern) (selected : d117650 q = 0) : d119328 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d117650, d119328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117650, d119328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9015 q selected
  have h13 (q : Pattern) (selected : d117651 q = 0) : d119329 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d117651, d119329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d117651, d119329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d117652 q = 0) : d119330 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d117652, d119330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d117652, d119330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d117653 q = 0) : d119331 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d117653, d119331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d117653, d119331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d117654 q = 0) : d119332 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d117654, d119332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d117654, d119332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d117767 q = 0) : d119410 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d117767, d119410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117767, d119410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9034 q selected
  have h18 (q : Pattern) (selected : d117778 q = 0) : d119417 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d117778, d119417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117778, d119417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9036 q selected
  have h19 (q : Pattern) (selected : d117779 q = 0) : d119418 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d117779, d119418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d117779, d119418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d117780 q = 0) : d119419 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d117780, d119419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d117780, d119419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d117781 q = 0) : d119420 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d117781, d119420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d117781, d119420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d117782 q = 0) : d119421 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d117782, d119421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d117782, d119421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d117783 q = 0) : d119422 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d117783, d119422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d117783, d119422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro9038 (p : Pattern) (selected : d117789 p = 0) : d119428 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117784 q = 0) : d119423 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d117784, d119423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117784, d119423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9037 q selected
  have h2 (q : Pattern) (selected : d117785 q = 0) : d119424 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d117785, d119424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117785, d119424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117786 q = 0) : d119425 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d117786, d119425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117786, d119425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117787 q = 0) : d119426 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d117787, d119426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117787, d119426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117788 q = 0) : d119427 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d117788, d119427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117788, d119427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117789 q = 0) : d119428 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d117789, d119428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117789, d119428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9039 (p : Pattern) (selected : d1553 p = 0) : d52994 p = 1 := by
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
  have h4 (q : Pattern) (selected : d1543 q = 0) : d52984 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro463 q selected
    | true =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro464 q selected
  have h5 (q : Pattern) (selected : d1544 q = 0) : d52985 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro385 q selected
  have h6 (q : Pattern) (selected : d1545 q = 0) : d52986 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1546 q = 0) : d52987 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1546, d52987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1546, d52987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1534 q = 0) : d52975 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1534, d52975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro462 q selected
    | true =>
      simp only [d1534, d52975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d1535 q = 0) : d52976 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1535, d52976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1535, d52976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d1549 q = 0) : d52990 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1549, d52990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro465 q selected
    | true =>
      simp only [d1549, d52990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h11 (q : Pattern) (selected : d1550 q = 0) : d52991 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1550, d52991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d1550, d52991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h12 (q : Pattern) (selected : d1551 q = 0) : d52992 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1551, d52992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d1551, d52992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d1552 q = 0) : d52993 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1552, d52993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1552, d52993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d1553 q = 0) : d52994 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1553, d52994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d1553, d52994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h14 p selected
theorem eqIntro9040 (p : Pattern) (selected : d1568 p = 0) : d53009 p = 1 := by
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
  have h4 (q : Pattern) (selected : d1560 q = 0) : d53001 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1560, d53001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro465 q selected
    | true =>
      simp only [d1560, d53001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro467 q selected
  have h5 (q : Pattern) (selected : d1115 q = 0) : d52696 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
  have h6 (q : Pattern) (selected : d1561 q = 0) : d53002 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1561, d53002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1561, d53002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1562 q = 0) : d53003 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1562, d53003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1562, d53003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1549 q = 0) : d52990 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1549, d52990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro465 q selected
    | true =>
      simp only [d1549, d52990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d1550 q = 0) : d52991 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1550, d52991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1550, d52991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d1564 q = 0) : d53005 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro468 q selected
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h11 (q : Pattern) (selected : d1565 q = 0) : d53006 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h12 (q : Pattern) (selected : d1566 q = 0) : d53007 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1566, d53007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d1566, d53007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d1567 q = 0) : d53008 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1567, d53008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1567, d53008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d1568 q = 0) : d53009 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1568, d53009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d1568, d53009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h14 p selected
theorem eqIntro9041 (p : Pattern) (selected : d117801 p = 0) : d119440 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117793 q = 0) : d119432 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117793, d119432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9039 q selected
    | true =>
      simp only [d117793, d119432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117794 q = 0) : d119433 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117794, d119433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117794, d119433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117795 q = 0) : d119434 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117795, d119434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117795, d119434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117796 q = 0) : d119435 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117796, d119435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117796, d119435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117797 q = 0) : d119436 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117797, d119436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9040 q selected
    | true =>
      simp only [d117797, d119436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117798 q = 0) : d119437 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117798, d119437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117798, d119437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117799 q = 0) : d119438 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117799, d119438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117799, d119438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117800 q = 0) : d119439 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117800, d119439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117800, d119439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117801 q = 0) : d119440 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117801, d119440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117801, d119440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro9042 (p : Pattern) (selected : d1580 p = 0) : d53021 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1575 q = 0) : d53016 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1575, d53016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1575, d53016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro467 q selected
  have h2 (q : Pattern) (selected : d1115 q = 0) : d52696 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
  have h3 (q : Pattern) (selected : d1576 q = 0) : d53017 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1576, d53017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1576, d53017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
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
  have h6 (q : Pattern) (selected : d1577 q = 0) : d53018 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1577, d53018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1577, d53018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1578 q = 0) : d53019 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1578, d53019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1578, d53019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d1579 q = 0) : d53020 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1579, d53020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1579, d53020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d1580 q = 0) : d53021 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1580, d53021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1580, d53021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro9043 (p : Pattern) (selected : d117806 p = 0) : d119445 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117797 q = 0) : d119436 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117797, d119436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9040 q selected
    | true =>
      simp only [d117797, d119436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117798 q = 0) : d119437 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117798, d119437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117798, d119437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117799 q = 0) : d119438 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117799, d119438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117799, d119438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117800 q = 0) : d119439 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117800, d119439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117800, d119439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117802 q = 0) : d119441 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117802, d119441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9042 q selected
    | true =>
      simp only [d117802, d119441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117803 q = 0) : d119442 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117803, d119442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117803, d119442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117804 q = 0) : d119443 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117804, d119443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117804, d119443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117805 q = 0) : d119444 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117805, d119444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117805, d119444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117806 q = 0) : d119445 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117806, d119445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117806, d119445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro9044 (p : Pattern) (selected : d5132 p = 0) : d69219 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d5128 q = 0) : d69215 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, d69215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5128, d69215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro468 q selected
  have h2 (q : Pattern) (selected : d5129 q = 0) : d69216 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5129, d69216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d5129, d69216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1564 q = 0) : d53005 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro468 q selected
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1565 q = 0) : d53006 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d5130 q = 0) : d69217 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5130, d69217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d5130, d69217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1578 q = 0) : d53019 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1578, d53019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1578, d53019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d5131 q = 0) : d69218 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5131, d69218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d5131, d69218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d5132 q = 0) : d69219 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5132, d69219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d5132, d69219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9045 (p : Pattern) (selected : d117814 p = 0) : d119453 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117810 q = 0) : d119449 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117810, d119449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9044 q selected
    | true =>
      simp only [d117810, d119449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117811 q = 0) : d119450 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117811, d119450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117811, d119450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117812 q = 0) : d119451 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117812, d119451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117812, d119451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117813 q = 0) : d119452 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117813, d119452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117813, d119452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117814 q = 0) : d119453 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117814, d119453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117814, d119453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro9046 (p : Pattern) (selected : d117819 p = 0) : d119458 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117802 q = 0) : d119441 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117802, d119441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9042 q selected
    | true =>
      simp only [d117802, d119441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117803 q = 0) : d119442 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117803, d119442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117803, d119442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117804 q = 0) : d119443 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117804, d119443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117804, d119443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117805 q = 0) : d119444 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117805, d119444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117805, d119444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117819 q = 0) : d119458 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117819, d119458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117819, d119458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro9047 (p : Pattern) (selected : d117825 p = 0) : d119464 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117807 q = 0) : d119446 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117807, d119446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9041 q selected
    | true =>
      simp only [d117807, d119446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9043 q selected
  have h2 (q : Pattern) (selected : d117808 q = 0) : d119447 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117808, d119447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117808, d119447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117809 q = 0) : d119448 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117809, d119448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117809, d119448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117815 q = 0) : d119454 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117815, d119454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9043 q selected
    | true =>
      simp only [d117815, d119454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9045 q selected
  have h5 (q : Pattern) (selected : d117816 q = 0) : d119455 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117816, d119455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117816, d119455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117817 q = 0) : d119456 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117817, d119456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117817, d119456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117818 q = 0) : d119457 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117818, d119457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117818, d119457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117820 q = 0) : d119459 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117820, d119459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9043 q selected
    | true =>
      simp only [d117820, d119459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9046 q selected
  have h9 (q : Pattern) (selected : d117821 q = 0) : d119460 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117821, d119460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117821, d119460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117822 q = 0) : d119461 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117822, d119461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117822, d119461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d117823 q = 0) : d119462 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117823, d119462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d117823, d119462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d117824 q = 0) : d119463 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117824, d119463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117824, d119463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d117825 q = 0) : d119464 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117825, d119464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d117825, d119464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro9048 (p : Pattern) (selected : d117829 p = 0) : d119468 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117820 q = 0) : d119459 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117820, d119459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9043 q selected
    | true =>
      simp only [d117820, d119459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9046 q selected
  have h2 (q : Pattern) (selected : d117821 q = 0) : d119460 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117821, d119460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117821, d119460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117822 q = 0) : d119461 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117822, d119461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117822, d119461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117823 q = 0) : d119462 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117823, d119462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117823, d119462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117828 q = 0) : d119467 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117828, d119467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117828, d119467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117829 q = 0) : d119468 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117829, d119468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117829, d119468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9049 (p : Pattern) (selected : d117835 p = 0) : d119474 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117826 q = 0) : d119465 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117826, d119465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9047 q selected
    | true =>
      simp only [d117826, d119465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117827 q = 0) : d119466 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117827, d119466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117827, d119466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117830 q = 0) : d119469 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117830, d119469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9048 q selected
    | true =>
      simp only [d117830, d119469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117831 q = 0) : d119470 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117831, d119470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117831, d119470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117832 q = 0) : d119471 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117832, d119471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117832, d119471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117833 q = 0) : d119472 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117833, d119472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117833, d119472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117834 q = 0) : d119473 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117834, d119473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117834, d119473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117835 q = 0) : d119474 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117835, d119474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117835, d119474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9050 (p : Pattern) (selected : d117839 p = 0) : d119478 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117830 q = 0) : d119469 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117830, d119469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9048 q selected
    | true =>
      simp only [d117830, d119469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117831 q = 0) : d119470 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117831, d119470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117831, d119470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117836 q = 0) : d119475 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117836, d119475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117836, d119475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117837 q = 0) : d119476 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117837, d119476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117837, d119476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117838 q = 0) : d119477 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117838, d119477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117838, d119477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117839 q = 0) : d119478 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117839, d119478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117839, d119478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9051 (p : Pattern) (selected : d117845 p = 0) : d119484 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117840 q = 0) : d119479 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117840, d119479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9049 q selected
    | true =>
      simp only [d117840, d119479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9050 q selected
  have h2 (q : Pattern) (selected : d117841 q = 0) : d119480 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117841, d119480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117841, d119480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117842 q = 0) : d119481 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117842, d119481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117842, d119481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117843 q = 0) : d119482 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117843, d119482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117843, d119482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117844 q = 0) : d119483 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117844, d119483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117844, d119483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117845 q = 0) : d119484 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117845, d119484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117845, d119484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9052 (p : Pattern) (selected : d117848 p = 0) : d119487 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117826 q = 0) : d119465 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117826, d119465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9047 q selected
    | true =>
      simp only [d117826, d119465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117827 q = 0) : d119466 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117827, d119466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117827, d119466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117830 q = 0) : d119469 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117830, d119469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9048 q selected
    | true =>
      simp only [d117830, d119469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117831 q = 0) : d119470 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117831, d119470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117831, d119470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117832 q = 0) : d119471 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117832, d119471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117832, d119471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117833 q = 0) : d119472 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117833, d119472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117833, d119472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117834 q = 0) : d119473 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117834, d119473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117834, d119473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117848 q = 0) : d119487 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117848, d119487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117848, d119487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9053 (p : Pattern) (selected : d117849 p = 0) : d119488 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117830 q = 0) : d119469 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117830, d119469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9048 q selected
    | true =>
      simp only [d117830, d119469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117831 q = 0) : d119470 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117831, d119470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117831, d119470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117836 q = 0) : d119475 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117836, d119475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117836, d119475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117837 q = 0) : d119476 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117837, d119476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117837, d119476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117838 q = 0) : d119477 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117838, d119477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117838, d119477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117849 q = 0) : d119488 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117849, d119488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117849, d119488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9054 (p : Pattern) (selected : d117855 p = 0) : d119494 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117840 q = 0) : d119479 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117840, d119479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9049 q selected
    | true =>
      simp only [d117840, d119479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9050 q selected
  have h2 (q : Pattern) (selected : d117841 q = 0) : d119480 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117841, d119480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117841, d119480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117842 q = 0) : d119481 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117842, d119481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117842, d119481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117843 q = 0) : d119482 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117843, d119482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117843, d119482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117844 q = 0) : d119483 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117844, d119483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117844, d119483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117850 q = 0) : d119489 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117850, d119489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9052 q selected
    | true =>
      simp only [d117850, d119489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9053 q selected
  have h7 (q : Pattern) (selected : d117851 q = 0) : d119490 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117851, d119490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117851, d119490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117852 q = 0) : d119491 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117852, d119491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117852, d119491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117853 q = 0) : d119492 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117853, d119492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117853, d119492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117854 q = 0) : d119493 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117854, d119493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117854, d119493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d117855 q = 0) : d119494 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117855, d119494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117855, d119494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro9055 (p : Pattern) (selected : d117860 p = 0) : d119499 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117826 q = 0) : d119465 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117826, d119465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9047 q selected
    | true =>
      simp only [d117826, d119465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117827 q = 0) : d119466 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117827, d119466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117827, d119466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117830 q = 0) : d119469 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117830, d119469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9048 q selected
    | true =>
      simp only [d117830, d119469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117831 q = 0) : d119470 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117831, d119470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117831, d119470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117832 q = 0) : d119471 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117832, d119471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117832, d119471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117833 q = 0) : d119472 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117833, d119472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117833, d119472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117859 q = 0) : d119498 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117859, d119498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117859, d119498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117860 q = 0) : d119499 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117860, d119499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117860, d119499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9056 (p : Pattern) (selected : d117862 p = 0) : d119501 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117830 q = 0) : d119469 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117830, d119469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9048 q selected
    | true =>
      simp only [d117830, d119469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117831 q = 0) : d119470 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117831, d119470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117831, d119470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117836 q = 0) : d119475 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117836, d119475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117836, d119475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117837 q = 0) : d119476 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117837, d119476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117837, d119476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117861 q = 0) : d119500 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117861, d119500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117861, d119500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117862 q = 0) : d119501 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117862, d119501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117862, d119501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9057 (p : Pattern) (selected : d117869 p = 0) : d119508 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117826 q = 0) : d119465 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117826, d119465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9047 q selected
    | true =>
      simp only [d117826, d119465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117827 q = 0) : d119466 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117827, d119466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117827, d119466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117830 q = 0) : d119469 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117830, d119469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9048 q selected
    | true =>
      simp only [d117830, d119469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117831 q = 0) : d119470 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117831, d119470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117831, d119470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117832 q = 0) : d119471 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117832, d119471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117832, d119471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117867 q = 0) : d119506 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117867, d119506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117867, d119506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117868 q = 0) : d119507 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117868, d119507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117868, d119507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117869 q = 0) : d119508 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117869, d119508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117869, d119508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9058 (p : Pattern) (selected : d117872 p = 0) : d119511 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117830 q = 0) : d119469 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117830, d119469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9048 q selected
    | true =>
      simp only [d117830, d119469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117831 q = 0) : d119470 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117831, d119470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117831, d119470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117836 q = 0) : d119475 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117836, d119475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117836, d119475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117870 q = 0) : d119509 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117870, d119509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117870, d119509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117871 q = 0) : d119510 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117871, d119510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117871, d119510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117872 q = 0) : d119511 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117872, d119511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117872, d119511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9059 (p : Pattern) (selected : d1538 p = 0) : d52979 p = 1 := by
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
  have h3 (q : Pattern) (selected : d1527 q = 0) : d52968 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro460 q selected
    | true =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro461 q selected
  have h4 (q : Pattern) (selected : d1528 q = 0) : d52969 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro384 q selected
  have h5 (q : Pattern) (selected : d1529 q = 0) : d52970 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1530 q = 0) : d52971 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1530, d52971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1530, d52971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1204 q = 0) : d52785 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1204, d52785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro406 q selected
    | true =>
      simp only [d1204, d52785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d1205 q = 0) : d52786 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1205, d52786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1205, d52786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1534 q = 0) : d52975 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1534, d52975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro462 q selected
    | true =>
      simp only [d1534, d52975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d1535 q = 0) : d52976 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1535, d52976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d1535, d52976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d1536 q = 0) : d52977 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1536, d52977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1536, d52977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d1537 q = 0) : d52978 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1537, d52978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1537, d52978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d1538 q = 0) : d52979 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1538, d52979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d1538, d52979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro9060 (p : Pattern) (selected : d117880 p = 0) : d119519 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117876 q = 0) : d119515 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117876, d119515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9059 q selected
    | true =>
      simp only [d117876, d119515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117877 q = 0) : d119516 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117877, d119516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117877, d119516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117878 q = 0) : d119517 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117878, d119517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117878, d119517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117879 q = 0) : d119518 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117879, d119518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117879, d119518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117793 q = 0) : d119432 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117793, d119432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9039 q selected
    | true =>
      simp only [d117793, d119432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117794 q = 0) : d119433 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117794, d119433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117794, d119433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117795 q = 0) : d119434 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117795, d119434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117795, d119434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117796 q = 0) : d119435 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117796, d119435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117796, d119435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117880 q = 0) : d119519 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117880, d119519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117880, d119519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro9061 (p : Pattern) (selected : d10061 p = 0) : d101488 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10055 q = 0) : d101482 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6713 q selected
  have h2 (q : Pattern) (selected : d10056 q = 0) : d101483 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10056, d101483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10056, d101483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10057 q = 0) : d101484 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10057, d101484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2813 q selected
    | true =>
      simp only [d10057, d101484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10058 q = 0) : d101485 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10058, d101485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10058, d101485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10059 q = 0) : d101486 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10059, d101486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10059, d101486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10060 q = 0) : d101487 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10060, d101487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10060, d101487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10061 q = 0) : d101488 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10061, d101488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10061, d101488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro9062 (p : Pattern) (selected : d117888 p = 0) : d119527 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117884 q = 0) : d119523 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117884, d119523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9061 q selected
    | true =>
      simp only [d117884, d119523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117885 q = 0) : d119524 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117885, d119524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117885, d119524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117886 q = 0) : d119525 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117886, d119525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117886, d119525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117887 q = 0) : d119526 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117887, d119526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117887, d119526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117888 q = 0) : d119527 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117888, d119527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117888, d119527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro9063 (p : Pattern) (selected : d117894 p = 0) : d119533 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117881 q = 0) : d119520 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117881, d119520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9060 q selected
    | true =>
      simp only [d117881, d119520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9041 q selected
  have h2 (q : Pattern) (selected : d117882 q = 0) : d119521 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117882, d119521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117882, d119521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117883 q = 0) : d119522 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117883, d119522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117883, d119522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117889 q = 0) : d119528 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117889, d119528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9041 q selected
    | true =>
      simp only [d117889, d119528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9062 q selected
  have h5 (q : Pattern) (selected : d117890 q = 0) : d119529 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117890, d119529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117890, d119529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117891 q = 0) : d119530 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117891, d119530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117891, d119530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117892 q = 0) : d119531 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117892, d119531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117892, d119531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117807 q = 0) : d119446 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117807, d119446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9041 q selected
    | true =>
      simp only [d117807, d119446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9043 q selected
  have h9 (q : Pattern) (selected : d117808 q = 0) : d119447 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117808, d119447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117808, d119447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117809 q = 0) : d119448 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117809, d119448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117809, d119448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d117815 q = 0) : d119454 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117815, d119454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9043 q selected
    | true =>
      simp only [d117815, d119454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9045 q selected
  have h12 (q : Pattern) (selected : d117816 q = 0) : d119455 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117816, d119455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117816, d119455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d117817 q = 0) : d119456 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117817, d119456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117817, d119456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d117818 q = 0) : d119457 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117818, d119457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d117818, d119457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d117893 q = 0) : d119532 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117893, d119532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117893, d119532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d117894 q = 0) : d119533 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117894, d119533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d117894, d119533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro9064 (p : Pattern) (selected : d117899 p = 0) : d119538 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117807 q = 0) : d119446 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117807, d119446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9041 q selected
    | true =>
      simp only [d117807, d119446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9043 q selected
  have h2 (q : Pattern) (selected : d117808 q = 0) : d119447 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117808, d119447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117808, d119447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117809 q = 0) : d119448 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117809, d119448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117809, d119448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117815 q = 0) : d119454 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117815, d119454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9043 q selected
    | true =>
      simp only [d117815, d119454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9045 q selected
  have h5 (q : Pattern) (selected : d117816 q = 0) : d119455 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117816, d119455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117816, d119455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117817 q = 0) : d119456 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117817, d119456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117817, d119456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117818 q = 0) : d119457 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117818, d119457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117818, d119457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117897 q = 0) : d119536 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117897, d119536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117897, d119536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117898 q = 0) : d119537 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117898, d119537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117898, d119537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117899 q = 0) : d119538 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117899, d119538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117899, d119538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro9065 (p : Pattern) (selected : d117905 p = 0) : d119544 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117895 q = 0) : d119534 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117895, d119534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9063 q selected
    | true =>
      simp only [d117895, d119534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117896 q = 0) : d119535 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117896, d119535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117896, d119535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117900 q = 0) : d119539 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117900, d119539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9064 q selected
    | true =>
      simp only [d117900, d119539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117901 q = 0) : d119540 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117901, d119540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117901, d119540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117902 q = 0) : d119541 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117902, d119541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117902, d119541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117903 q = 0) : d119542 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117903, d119542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117903, d119542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117904 q = 0) : d119543 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117904, d119543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117904, d119543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117905 q = 0) : d119544 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117905, d119544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117905, d119544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9066 (p : Pattern) (selected : d117909 p = 0) : d119548 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117900 q = 0) : d119539 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117900, d119539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9064 q selected
    | true =>
      simp only [d117900, d119539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117901 q = 0) : d119540 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117901, d119540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117901, d119540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117830 q = 0) : d119469 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117830, d119469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9048 q selected
    | true =>
      simp only [d117830, d119469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117831 q = 0) : d119470 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117831, d119470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117831, d119470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117906 q = 0) : d119545 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117906, d119545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117906, d119545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117907 q = 0) : d119546 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117907, d119546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117907, d119546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117908 q = 0) : d119547 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117908, d119547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117908, d119547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117909 q = 0) : d119548 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117909, d119548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117909, d119548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9067 (p : Pattern) (selected : d1724 p = 0) : d52994 p = 1 := by
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
  have h4 (q : Pattern) (selected : d1714 q = 0) : d52984 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1714, d52984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro496 q selected
    | true =>
      simp only [d1714, d52984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro497 q selected
  have h5 (q : Pattern) (selected : d1715 q = 0) : d52985 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1715, d52985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1715, d52985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro414 q selected
  have h6 (q : Pattern) (selected : d1716 q = 0) : d52986 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1716, d52986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1716, d52986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1717 q = 0) : d52987 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1717, d52987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1717, d52987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1705 q = 0) : d52975 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1705, d52975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro495 q selected
    | true =>
      simp only [d1705, d52975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d1706 q = 0) : d52976 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1706, d52976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1706, d52976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d1720 q = 0) : d52990 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1720, d52990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro498 q selected
    | true =>
      simp only [d1720, d52990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h11 (q : Pattern) (selected : d1721 q = 0) : d52991 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1721, d52991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d1721, d52991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h12 (q : Pattern) (selected : d1722 q = 0) : d52992 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1722, d52992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d1722, d52992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d1723 q = 0) : d52993 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1723, d52993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1723, d52993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d1724 q = 0) : d52994 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1724, d52994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d1724, d52994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h14 p selected
theorem eqIntro9068 (p : Pattern) (selected : d1739 p = 0) : d53009 p = 1 := by
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
  have h4 (q : Pattern) (selected : d1731 q = 0) : d53001 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1731, d53001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro498 q selected
    | true =>
      simp only [d1731, d53001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro500 q selected
  have h5 (q : Pattern) (selected : d1270 q = 0) : d52696 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1270, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1270, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
  have h6 (q : Pattern) (selected : d1732 q = 0) : d53002 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1732, d53002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1732, d53002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1733 q = 0) : d53003 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1733, d53003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1733, d53003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1720 q = 0) : d52990 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1720, d52990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro498 q selected
    | true =>
      simp only [d1720, d52990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d1721 q = 0) : d52991 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1721, d52991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1721, d52991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d1735 q = 0) : d53005 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1735, d53005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro501 q selected
    | true =>
      simp only [d1735, d53005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h11 (q : Pattern) (selected : d1736 q = 0) : d53006 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1736, d53006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d1736, d53006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h12 (q : Pattern) (selected : d1737 q = 0) : d53007 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1737, d53007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d1737, d53007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d1738 q = 0) : d53008 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1738, d53008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1738, d53008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d1739 q = 0) : d53009 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1739, d53009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d1739, d53009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h14 p selected
theorem eqIntro9069 (p : Pattern) (selected : d117919 p = 0) : d119440 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117911 q = 0) : d119432 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117911, d119432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9067 q selected
    | true =>
      simp only [d117911, d119432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117912 q = 0) : d119433 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117912, d119433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117912, d119433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117913 q = 0) : d119434 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117913, d119434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117913, d119434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117914 q = 0) : d119435 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117914, d119435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117914, d119435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117915 q = 0) : d119436 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117915, d119436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9068 q selected
    | true =>
      simp only [d117915, d119436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117916 q = 0) : d119437 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117916, d119437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117916, d119437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117917 q = 0) : d119438 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117917, d119438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117917, d119438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117918 q = 0) : d119439 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117918, d119439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117918, d119439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117919 q = 0) : d119440 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117919, d119440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117919, d119440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro9070 (p : Pattern) (selected : d1751 p = 0) : d53021 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1746 q = 0) : d53016 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1746, d53016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1746, d53016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro500 q selected
  have h2 (q : Pattern) (selected : d1270 q = 0) : d52696 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1270, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1270, d52696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
  have h3 (q : Pattern) (selected : d1747 q = 0) : d53017 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1747, d53017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1747, d53017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1735 q = 0) : d53005 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1735, d53005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro501 q selected
    | true =>
      simp only [d1735, d53005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1736 q = 0) : d53006 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1736, d53006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1736, d53006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d1748 q = 0) : d53018 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1748, d53018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1748, d53018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1749 q = 0) : d53019 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1749, d53019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1749, d53019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d1750 q = 0) : d53020 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1750, d53020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1750, d53020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d1751 q = 0) : d53021 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1751, d53021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1751, d53021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro9071 (p : Pattern) (selected : d117924 p = 0) : d119445 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117915 q = 0) : d119436 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117915, d119436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9068 q selected
    | true =>
      simp only [d117915, d119436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117916 q = 0) : d119437 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117916, d119437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117916, d119437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117917 q = 0) : d119438 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117917, d119438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117917, d119438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117918 q = 0) : d119439 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117918, d119439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117918, d119439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117920 q = 0) : d119441 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117920, d119441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9070 q selected
    | true =>
      simp only [d117920, d119441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117921 q = 0) : d119442 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117921, d119442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117921, d119442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117922 q = 0) : d119443 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117922, d119443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117922, d119443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117923 q = 0) : d119444 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117923, d119444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117923, d119444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117924 q = 0) : d119445 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117924, d119445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117924, d119445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro9072 (p : Pattern) (selected : d10213 p = 0) : d69219 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10209 q = 0) : d69215 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10209, d69215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10209, d69215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro501 q selected
  have h2 (q : Pattern) (selected : d10210 q = 0) : d69216 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10210, d69216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10210, d69216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1735 q = 0) : d53005 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1735, d53005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro501 q selected
    | true =>
      simp only [d1735, d53005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1736 q = 0) : d53006 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1736, d53006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1736, d53006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10211 q = 0) : d69217 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10211, d69217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10211, d69217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1749 q = 0) : d53019 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1749, d53019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1749, d53019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10212 q = 0) : d69218 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10212, d69218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10212, d69218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10213 q = 0) : d69219 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10213, d69219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10213, d69219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9073 (p : Pattern) (selected : d117932 p = 0) : d119453 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117928 q = 0) : d119449 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117928, d119449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9072 q selected
    | true =>
      simp only [d117928, d119449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117929 q = 0) : d119450 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117929, d119450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117929, d119450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117930 q = 0) : d119451 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117930, d119451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117930, d119451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117931 q = 0) : d119452 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117931, d119452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117931, d119452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117932 q = 0) : d119453 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117932, d119453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117932, d119453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro9074 (p : Pattern) (selected : d117937 p = 0) : d119458 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117920 q = 0) : d119441 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117920, d119441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9070 q selected
    | true =>
      simp only [d117920, d119441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117921 q = 0) : d119442 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117921, d119442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117921, d119442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117922 q = 0) : d119443 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117922, d119443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117922, d119443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117923 q = 0) : d119444 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117923, d119444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117923, d119444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117937 q = 0) : d119458 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117937, d119458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117937, d119458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro9075 (p : Pattern) (selected : d117943 p = 0) : d119464 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117925 q = 0) : d119446 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117925, d119446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9069 q selected
    | true =>
      simp only [d117925, d119446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9071 q selected
  have h2 (q : Pattern) (selected : d117926 q = 0) : d119447 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117926, d119447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117926, d119447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117927 q = 0) : d119448 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117927, d119448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117927, d119448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117933 q = 0) : d119454 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117933, d119454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9071 q selected
    | true =>
      simp only [d117933, d119454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9073 q selected
  have h5 (q : Pattern) (selected : d117934 q = 0) : d119455 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117934, d119455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117934, d119455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117935 q = 0) : d119456 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117935, d119456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117935, d119456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117936 q = 0) : d119457 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117936, d119457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117936, d119457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117938 q = 0) : d119459 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117938, d119459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9071 q selected
    | true =>
      simp only [d117938, d119459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9074 q selected
  have h9 (q : Pattern) (selected : d117939 q = 0) : d119460 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117939, d119460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117939, d119460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117940 q = 0) : d119461 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117940, d119461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117940, d119461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d117941 q = 0) : d119462 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117941, d119462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d117941, d119462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d117942 q = 0) : d119463 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117942, d119463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117942, d119463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d117943 q = 0) : d119464 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117943, d119464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d117943, d119464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro9076 (p : Pattern) (selected : d117947 p = 0) : d119468 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117938 q = 0) : d119459 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117938, d119459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9071 q selected
    | true =>
      simp only [d117938, d119459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9074 q selected
  have h2 (q : Pattern) (selected : d117939 q = 0) : d119460 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117939, d119460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117939, d119460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117940 q = 0) : d119461 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117940, d119461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117940, d119461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117941 q = 0) : d119462 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117941, d119462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117941, d119462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117946 q = 0) : d119467 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117946, d119467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117946, d119467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117947 q = 0) : d119468 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117947, d119468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117947, d119468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9077 (p : Pattern) (selected : d117953 p = 0) : d119474 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117944 q = 0) : d119465 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117944, d119465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9075 q selected
    | true =>
      simp only [d117944, d119465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117945 q = 0) : d119466 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117945, d119466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117945, d119466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117948 q = 0) : d119469 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117948, d119469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9076 q selected
    | true =>
      simp only [d117948, d119469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117949 q = 0) : d119470 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117949, d119470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117949, d119470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117950 q = 0) : d119471 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117950, d119471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117950, d119471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117951 q = 0) : d119472 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117951, d119472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117951, d119472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117952 q = 0) : d119473 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117952, d119473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117952, d119473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117953 q = 0) : d119474 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117953, d119474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117953, d119474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9078 (p : Pattern) (selected : d117957 p = 0) : d119478 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117948 q = 0) : d119469 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117948, d119469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9076 q selected
    | true =>
      simp only [d117948, d119469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117949 q = 0) : d119470 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117949, d119470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117949, d119470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117954 q = 0) : d119475 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117954, d119475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117954, d119475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117955 q = 0) : d119476 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117955, d119476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117955, d119476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117956 q = 0) : d119477 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117956, d119477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117956, d119477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117957 q = 0) : d119478 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117957, d119478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117957, d119478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9079 (p : Pattern) (selected : d117963 p = 0) : d119554 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117826 q = 0) : d119465 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117826, d119465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9047 q selected
    | true =>
      simp only [d117826, d119465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117827 q = 0) : d119466 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117827, d119466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117827, d119466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117960 q = 0) : d119551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117960, d119551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117960, d119551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117961 q = 0) : d119552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117961, d119552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117961, d119552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117962 q = 0) : d119553 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117962, d119553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117962, d119553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117963 q = 0) : d119554 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117963, d119554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117963, d119554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9080 (p : Pattern) (selected : d117969 p = 0) : d119560 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117863 q = 0) : d119502 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117863, d119502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9055 q selected
    | true =>
      simp only [d117863, d119502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9056 q selected
  have h2 (q : Pattern) (selected : d117864 q = 0) : d119503 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117864, d119503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117864, d119503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117865 q = 0) : d119504 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117865, d119504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117865, d119504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117866 q = 0) : d119505 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117866, d119505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117866, d119505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117873 q = 0) : d119512 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117873, d119512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9057 q selected
    | true =>
      simp only [d117873, d119512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9058 q selected
  have h6 (q : Pattern) (selected : d117874 q = 0) : d119513 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117874, d119513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117874, d119513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117875 q = 0) : d119514 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117875, d119514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117875, d119514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117910 q = 0) : d119549 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117910, d119549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9065 q selected
    | true =>
      simp only [d117910, d119549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9066 q selected
  have h9 (q : Pattern) (selected : d117958 q = 0) : d119479 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117958, d119479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9077 q selected
    | true =>
      simp only [d117958, d119479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9078 q selected
  have h10 (q : Pattern) (selected : d117959 q = 0) : d119550 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117959, d119550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117959, d119550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d117964 q = 0) : d119555 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117964, d119555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9079 q selected
    | true =>
      simp only [d117964, d119555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d117965 q = 0) : d119556 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117965, d119556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d117965, d119556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d117966 q = 0) : d119557 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117966, d119557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d117966, d119557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d117967 q = 0) : d119558 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117967, d119558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117967, d119558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d117968 q = 0) : d119559 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117968, d119559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117968, d119559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d117969 q = 0) : d119560 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117969, d119560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117969, d119560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro9081 (p : Pattern) (selected : d117970 p = 0) : d119561 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117826 q = 0) : d119465 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117826, d119465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9047 q selected
    | true =>
      simp only [d117826, d119465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117827 q = 0) : d119466 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117827, d119466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117827, d119466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117830 q = 0) : d119469 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117830, d119469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9048 q selected
    | true =>
      simp only [d117830, d119469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117831 q = 0) : d119470 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117831, d119470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117831, d119470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117832 q = 0) : d119471 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117832, d119471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117832, d119471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117833 q = 0) : d119472 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117833, d119472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117833, d119472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117859 q = 0) : d119498 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117859, d119498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117859, d119498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117970 q = 0) : d119561 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117970, d119561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117970, d119561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9082 (p : Pattern) (selected : d117971 p = 0) : d119562 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117830 q = 0) : d119469 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117830, d119469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9048 q selected
    | true =>
      simp only [d117830, d119469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117831 q = 0) : d119470 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117831, d119470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117831, d119470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117836 q = 0) : d119475 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117836, d119475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117836, d119475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117837 q = 0) : d119476 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117837, d119476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117837, d119476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117861 q = 0) : d119500 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117861, d119500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117861, d119500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117971 q = 0) : d119562 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117971, d119562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117971, d119562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9083 (p : Pattern) (selected : d117976 p = 0) : d119567 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117826 q = 0) : d119465 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117826, d119465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9047 q selected
    | true =>
      simp only [d117826, d119465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117827 q = 0) : d119466 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117827, d119466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117827, d119466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117830 q = 0) : d119469 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117830, d119469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9048 q selected
    | true =>
      simp only [d117830, d119469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117831 q = 0) : d119470 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117831, d119470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117831, d119470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117832 q = 0) : d119471 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117832, d119471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117832, d119471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117867 q = 0) : d119506 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117867, d119506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117867, d119506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117868 q = 0) : d119507 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117868, d119507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117868, d119507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117976 q = 0) : d119567 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117976, d119567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117976, d119567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9084 (p : Pattern) (selected : d117977 p = 0) : d119568 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117830 q = 0) : d119469 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117830, d119469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9048 q selected
    | true =>
      simp only [d117830, d119469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117831 q = 0) : d119470 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117831, d119470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117831, d119470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117836 q = 0) : d119475 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117836, d119475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117836, d119475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117870 q = 0) : d119509 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117870, d119509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117870, d119509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117871 q = 0) : d119510 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117871, d119510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117871, d119510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117977 q = 0) : d119568 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117977, d119568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117977, d119568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9085 (p : Pattern) (selected : d117981 p = 0) : d119572 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117895 q = 0) : d119534 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117895, d119534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9063 q selected
    | true =>
      simp only [d117895, d119534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117896 q = 0) : d119535 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117896, d119535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117896, d119535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117900 q = 0) : d119539 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117900, d119539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9064 q selected
    | true =>
      simp only [d117900, d119539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117901 q = 0) : d119540 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117901, d119540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117901, d119540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117902 q = 0) : d119541 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117902, d119541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117902, d119541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117903 q = 0) : d119542 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117903, d119542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117903, d119542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117904 q = 0) : d119543 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117904, d119543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117904, d119543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117981 q = 0) : d119572 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117981, d119572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117981, d119572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9086 (p : Pattern) (selected : d117982 p = 0) : d119573 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117900 q = 0) : d119539 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117900, d119539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9064 q selected
    | true =>
      simp only [d117900, d119539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117901 q = 0) : d119540 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117901, d119540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117901, d119540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117830 q = 0) : d119469 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117830, d119469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9048 q selected
    | true =>
      simp only [d117830, d119469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117831 q = 0) : d119470 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117831, d119470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117831, d119470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117906 q = 0) : d119545 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117906, d119545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117906, d119545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117907 q = 0) : d119546 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117907, d119546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117907, d119546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117908 q = 0) : d119547 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117908, d119547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117908, d119547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117982 q = 0) : d119573 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117982, d119573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117982, d119573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9087 (p : Pattern) (selected : d117984 p = 0) : d119487 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117944 q = 0) : d119465 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117944, d119465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9075 q selected
    | true =>
      simp only [d117944, d119465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117945 q = 0) : d119466 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117945, d119466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117945, d119466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117948 q = 0) : d119469 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117948, d119469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9076 q selected
    | true =>
      simp only [d117948, d119469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117949 q = 0) : d119470 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117949, d119470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117949, d119470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117950 q = 0) : d119471 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117950, d119471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117950, d119471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117951 q = 0) : d119472 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117951, d119472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117951, d119472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117952 q = 0) : d119473 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117952, d119473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117952, d119473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117984 q = 0) : d119487 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117984, d119487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117984, d119487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9088 (p : Pattern) (selected : d117985 p = 0) : d119488 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117948 q = 0) : d119469 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117948, d119469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9076 q selected
    | true =>
      simp only [d117948, d119469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117949 q = 0) : d119470 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117949, d119470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117949, d119470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117954 q = 0) : d119475 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117954, d119475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117954, d119475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117955 q = 0) : d119476 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117955, d119476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117955, d119476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117956 q = 0) : d119477 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117956, d119477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117956, d119477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117985 q = 0) : d119488 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117985, d119488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117985, d119488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9089 (p : Pattern) (selected : d117988 p = 0) : d119576 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117826 q = 0) : d119465 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117826, d119465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9047 q selected
    | true =>
      simp only [d117826, d119465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117827 q = 0) : d119466 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117827, d119466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117827, d119466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117960 q = 0) : d119551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117960, d119551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117960, d119551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117961 q = 0) : d119552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117961, d119552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117961, d119552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117962 q = 0) : d119553 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117962, d119553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117962, d119553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117988 q = 0) : d119576 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117988, d119576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117988, d119576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9090 (p : Pattern) (selected : d117994 p = 0) : d119582 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117863 q = 0) : d119502 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117863, d119502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9055 q selected
    | true =>
      simp only [d117863, d119502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9056 q selected
  have h2 (q : Pattern) (selected : d117864 q = 0) : d119503 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117864, d119503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117864, d119503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117865 q = 0) : d119504 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117865, d119504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117865, d119504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117866 q = 0) : d119505 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117866, d119505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117866, d119505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117873 q = 0) : d119512 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117873, d119512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9057 q selected
    | true =>
      simp only [d117873, d119512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9058 q selected
  have h6 (q : Pattern) (selected : d117874 q = 0) : d119513 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117874, d119513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117874, d119513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117875 q = 0) : d119514 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117875, d119514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117875, d119514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117910 q = 0) : d119549 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117910, d119549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9065 q selected
    | true =>
      simp only [d117910, d119549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9066 q selected
  have h9 (q : Pattern) (selected : d117958 q = 0) : d119479 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117958, d119479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9077 q selected
    | true =>
      simp only [d117958, d119479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9078 q selected
  have h10 (q : Pattern) (selected : d117959 q = 0) : d119550 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117959, d119550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117959, d119550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d117964 q = 0) : d119555 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117964, d119555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9079 q selected
    | true =>
      simp only [d117964, d119555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d117965 q = 0) : d119556 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117965, d119556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d117965, d119556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d117966 q = 0) : d119557 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117966, d119557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d117966, d119557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d117967 q = 0) : d119558 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117967, d119558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117967, d119558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d117968 q = 0) : d119559 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117968, d119559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117968, d119559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d117972 q = 0) : d119563 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117972, d119563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9081 q selected
    | true =>
      simp only [d117972, d119563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9082 q selected
  have h17 (q : Pattern) (selected : d117973 q = 0) : d119564 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117973, d119564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117973, d119564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d117974 q = 0) : d119565 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117974, d119565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d117974, d119565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d117975 q = 0) : d119566 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117975, d119566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117975, d119566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d117978 q = 0) : d119569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117978, d119569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9083 q selected
    | true =>
      simp only [d117978, d119569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9084 q selected
  have h21 (q : Pattern) (selected : d117979 q = 0) : d119570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117979, d119570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117979, d119570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d117980 q = 0) : d119571 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117980, d119571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d117980, d119571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d117983 q = 0) : d119574 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117983, d119574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9085 q selected
    | true =>
      simp only [d117983, d119574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9086 q selected
  have h24 (q : Pattern) (selected : d117986 q = 0) : d119489 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117986, d119489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9087 q selected
    | true =>
      simp only [d117986, d119489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9088 q selected
  have h25 (q : Pattern) (selected : d117987 q = 0) : d119575 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117987, d119575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d117987, d119575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d117989 q = 0) : d119577 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117989, d119577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9089 q selected
    | true =>
      simp only [d117989, d119577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d117990 q = 0) : d119578 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117990, d119578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d117990, d119578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d117991 q = 0) : d119579 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117991, d119579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d117991, d119579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d117992 q = 0) : d119580 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117992, d119580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d117992, d119580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d117993 q = 0) : d119581 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117993, d119581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d117993, d119581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d117994 q = 0) : d119582 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117994, d119582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d117994, d119582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro9091 (p : Pattern) (selected : d118006 p = 0) : d119594 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117996 q = 0) : d119584 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117996, d119584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9066 q selected
    | true =>
      simp only [d117996, d119584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9050 q selected
  have h2 (q : Pattern) (selected : d117997 q = 0) : d119585 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117997, d119585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117997, d119585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117998 q = 0) : d119586 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117998, d119586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117998, d119586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117999 q = 0) : d119587 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117999, d119587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117999, d119587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118000 q = 0) : d119588 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118000, d119588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118000, d119588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118001 q = 0) : d119589 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118001, d119589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9050 q selected
    | true =>
      simp only [d118001, d119589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118002 q = 0) : d119590 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118002, d119590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118002, d119590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118003 q = 0) : d119591 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118003, d119591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118003, d119591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d118004 q = 0) : d119592 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118004, d119592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118004, d119592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d118005 q = 0) : d119593 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118005, d119593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118005, d119593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d118006 q = 0) : d119594 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118006, d119594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118006, d119594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro9092 (p : Pattern) (selected : d118012 p = 0) : d119600 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118001 q = 0) : d119589 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118001, d119589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9050 q selected
    | true =>
      simp only [d118001, d119589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118002 q = 0) : d119590 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118002, d119590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118002, d119590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118003 q = 0) : d119591 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118003, d119591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118003, d119591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118004 q = 0) : d119592 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118004, d119592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118004, d119592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118005 q = 0) : d119593 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118005, d119593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118005, d119593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118007 q = 0) : d119595 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118007, d119595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9053 q selected
    | true =>
      simp only [d118007, d119595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118008 q = 0) : d119596 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118008, d119596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118008, d119596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118009 q = 0) : d119597 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118009, d119597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118009, d119597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d118010 q = 0) : d119598 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118010, d119598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118010, d119598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d118011 q = 0) : d119599 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118011, d119599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118011, d119599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d118012 q = 0) : d119600 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118012, d119600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118012, d119600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro9093 (p : Pattern) (selected : d118019 p = 0) : d119607 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117983 q = 0) : d119574 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117983, d119574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9085 q selected
    | true =>
      simp only [d117983, d119574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9086 q selected
  have h2 (q : Pattern) (selected : d117986 q = 0) : d119489 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117986, d119489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9087 q selected
    | true =>
      simp only [d117986, d119489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9088 q selected
  have h3 (q : Pattern) (selected : d117987 q = 0) : d119575 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117987, d119575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117987, d119575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117989 q = 0) : d119577 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117989, d119577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9089 q selected
    | true =>
      simp only [d117989, d119577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117990 q = 0) : d119578 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117990, d119578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117990, d119578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117991 q = 0) : d119579 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117991, d119579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117991, d119579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d118017 q = 0) : d119605 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118017, d119605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118017, d119605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118018 q = 0) : d119606 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118018, d119606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118018, d119606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d118019 q = 0) : d119607 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118019, d119607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118019, d119607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro9094 (p : Pattern) (selected : d118021 p = 0) : d119609 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118007 q = 0) : d119595 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118007, d119595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9053 q selected
    | true =>
      simp only [d118007, d119595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118008 q = 0) : d119596 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118008, d119596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118008, d119596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118009 q = 0) : d119597 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118009, d119597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118009, d119597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118010 q = 0) : d119598 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118010, d119598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118010, d119598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118011 q = 0) : d119599 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118011, d119599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118011, d119599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118021 q = 0) : d119609 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118021, d119609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118021, d119609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9095 (p : Pattern) (selected : d118035 p = 0) : d119623 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118027 q = 0) : d119615 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118027, d119615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118027, d119615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9059 q selected
  have h2 (q : Pattern) (selected : d117876 q = 0) : d119515 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117876, d119515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9059 q selected
    | true =>
      simp only [d117876, d119515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118028 q = 0) : d119616 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118028, d119616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118028, d119616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117877 q = 0) : d119516 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117877, d119516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117877, d119516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118029 q = 0) : d119617 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118029, d119617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118029, d119617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118030 q = 0) : d119618 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118030, d119618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118030, d119618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118031 q = 0) : d119619 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118031, d119619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118031, d119619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9039 q selected
  have h8 (q : Pattern) (selected : d117793 q = 0) : d119432 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117793, d119432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9039 q selected
    | true =>
      simp only [d117793, d119432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d118032 q = 0) : d119620 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118032, d119620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118032, d119620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117794 q = 0) : d119433 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117794, d119433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117794, d119433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d118033 q = 0) : d119621 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118033, d119621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d118033, d119621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d118034 q = 0) : d119622 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118034, d119622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d118034, d119622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d118035 q = 0) : d119623 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118035, d119623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118035, d119623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro9096 (p : Pattern) (selected : d118040 p = 0) : d119628 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118031 q = 0) : d119619 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118031, d119619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118031, d119619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9039 q selected
  have h2 (q : Pattern) (selected : d117793 q = 0) : d119432 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117793, d119432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9039 q selected
    | true =>
      simp only [d117793, d119432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118032 q = 0) : d119620 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118032, d119620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118032, d119620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117794 q = 0) : d119433 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117794, d119433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117794, d119433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118033 q = 0) : d119621 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118033, d119621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118033, d119621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118034 q = 0) : d119622 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118034, d119622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118034, d119622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118036 q = 0) : d119624 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118036, d119624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118036, d119624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9040 q selected
  have h8 (q : Pattern) (selected : d117797 q = 0) : d119436 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117797, d119436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9040 q selected
    | true =>
      simp only [d117797, d119436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d118037 q = 0) : d119625 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118037, d119625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118037, d119625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117798 q = 0) : d119437 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117798, d119437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117798, d119437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d118038 q = 0) : d119626 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118038, d119626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d118038, d119626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d118039 q = 0) : d119627 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118039, d119627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d118039, d119627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d118040 q = 0) : d119628 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118040, d119628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118040, d119628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro9097 (p : Pattern) (selected : d118048 p = 0) : d119636 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118044 q = 0) : d119632 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118044, d119632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118044, d119632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9061 q selected
  have h2 (q : Pattern) (selected : d117884 q = 0) : d119523 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117884, d119523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9061 q selected
    | true =>
      simp only [d117884, d119523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118045 q = 0) : d119633 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118045, d119633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118045, d119633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117885 q = 0) : d119524 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117885, d119524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117885, d119524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118046 q = 0) : d119634 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118046, d119634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118046, d119634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118047 q = 0) : d119635 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118047, d119635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118047, d119635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118048 q = 0) : d119636 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118048, d119636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118048, d119636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro9098 (p : Pattern) (selected : d118057 p = 0) : d119645 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118036 q = 0) : d119624 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118036, d119624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118036, d119624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9040 q selected
  have h2 (q : Pattern) (selected : d117797 q = 0) : d119436 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117797, d119436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9040 q selected
    | true =>
      simp only [d117797, d119436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118037 q = 0) : d119625 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118037, d119625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118037, d119625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117798 q = 0) : d119437 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117798, d119437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117798, d119437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118038 q = 0) : d119626 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118038, d119626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118038, d119626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118039 q = 0) : d119627 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118039, d119627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118039, d119627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118053 q = 0) : d119641 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118053, d119641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118053, d119641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9042 q selected
  have h8 (q : Pattern) (selected : d117802 q = 0) : d119441 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117802, d119441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9042 q selected
    | true =>
      simp only [d117802, d119441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d118054 q = 0) : d119642 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118054, d119642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118054, d119642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117803 q = 0) : d119442 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117803, d119442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117803, d119442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d118055 q = 0) : d119643 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118055, d119643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d118055, d119643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d118056 q = 0) : d119644 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118056, d119644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d118056, d119644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d118057 q = 0) : d119645 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118057, d119645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118057, d119645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro9099 (p : Pattern) (selected : d118065 p = 0) : d119653 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118061 q = 0) : d119649 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118061, d119649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118061, d119649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9044 q selected
  have h2 (q : Pattern) (selected : d117810 q = 0) : d119449 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117810, d119449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9044 q selected
    | true =>
      simp only [d117810, d119449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118062 q = 0) : d119650 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118062, d119650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118062, d119650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117811 q = 0) : d119450 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117811, d119450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117811, d119450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118063 q = 0) : d119651 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118063, d119651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118063, d119651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118064 q = 0) : d119652 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118064, d119652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118064, d119652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118065 q = 0) : d119653 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118065, d119653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118065, d119653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro9100 (p : Pattern) (selected : d118071 p = 0) : d119659 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118041 q = 0) : d119629 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118041, d119629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9095 q selected
    | true =>
      simp only [d118041, d119629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9096 q selected
  have h2 (q : Pattern) (selected : d118042 q = 0) : d119630 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118042, d119630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118042, d119630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118043 q = 0) : d119631 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118043, d119631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118043, d119631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118049 q = 0) : d119637 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118049, d119637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9096 q selected
    | true =>
      simp only [d118049, d119637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9097 q selected
  have h5 (q : Pattern) (selected : d118050 q = 0) : d119638 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118050, d119638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118050, d119638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118051 q = 0) : d119639 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118051, d119639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118051, d119639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d118052 q = 0) : d119640 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118052, d119640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118052, d119640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118058 q = 0) : d119646 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118058, d119646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9096 q selected
    | true =>
      simp only [d118058, d119646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9098 q selected
  have h9 (q : Pattern) (selected : d118059 q = 0) : d119647 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118059, d119647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118059, d119647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d118060 q = 0) : d119648 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118060, d119648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118060, d119648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d118066 q = 0) : d119654 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118066, d119654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9098 q selected
    | true =>
      simp only [d118066, d119654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9099 q selected
  have h12 (q : Pattern) (selected : d118067 q = 0) : d119655 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118067, d119655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118067, d119655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d118068 q = 0) : d119656 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118068, d119656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118068, d119656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d118069 q = 0) : d119657 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118069, d119657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d118069, d119657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d118070 q = 0) : d119658 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d118070, d119658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118070, d119658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d118071 q = 0) : d119659 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d118071, d119659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d118071, d119659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro9101 (p : Pattern) (selected : d118076 p = 0) : d119664 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118058 q = 0) : d119646 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118058, d119646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9096 q selected
    | true =>
      simp only [d118058, d119646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9098 q selected
  have h2 (q : Pattern) (selected : d118059 q = 0) : d119647 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118059, d119647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118059, d119647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118060 q = 0) : d119648 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118060, d119648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118060, d119648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118066 q = 0) : d119654 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118066, d119654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9098 q selected
    | true =>
      simp only [d118066, d119654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9099 q selected
  have h5 (q : Pattern) (selected : d118067 q = 0) : d119655 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118067, d119655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118067, d119655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118068 q = 0) : d119656 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118068, d119656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118068, d119656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d118069 q = 0) : d119657 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118069, d119657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118069, d119657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118074 q = 0) : d119662 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118074, d119662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118074, d119662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d118075 q = 0) : d119663 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d118075, d119663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118075, d119663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d118076 q = 0) : d119664 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d118076, d119664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d118076, d119664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro9102 (p : Pattern) (selected : d118082 p = 0) : d119670 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118072 q = 0) : d119660 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118072, d119660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9100 q selected
    | true =>
      simp only [d118072, d119660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118073 q = 0) : d119661 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118073, d119661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118073, d119661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118077 q = 0) : d119665 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118077, d119665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9101 q selected
    | true =>
      simp only [d118077, d119665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118078 q = 0) : d119666 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118078, d119666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118078, d119666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118079 q = 0) : d119667 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118079, d119667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118079, d119667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118080 q = 0) : d119668 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118080, d119668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118080, d119668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118081 q = 0) : d119669 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118081, d119669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118081, d119669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d118082 q = 0) : d119670 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118082, d119670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118082, d119670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9103 (p : Pattern) (selected : d118083 p = 0) : d119671 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118053 q = 0) : d119641 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118053, d119641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118053, d119641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9042 q selected
  have h2 (q : Pattern) (selected : d117802 q = 0) : d119441 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117802, d119441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9042 q selected
    | true =>
      simp only [d117802, d119441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118054 q = 0) : d119642 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118054, d119642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118054, d119642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117803 q = 0) : d119442 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117803, d119442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117803, d119442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118055 q = 0) : d119643 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118055, d119643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118055, d119643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118056 q = 0) : d119644 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118056, d119644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118056, d119644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118083 q = 0) : d119671 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118083, d119671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118083, d119671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro9104 (p : Pattern) (selected : d118089 p = 0) : d119677 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118084 q = 0) : d119672 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118084, d119672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9098 q selected
    | true =>
      simp only [d118084, d119672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9103 q selected
  have h2 (q : Pattern) (selected : d118085 q = 0) : d119673 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118085, d119673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118085, d119673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118086 q = 0) : d119674 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118086, d119674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118086, d119674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118087 q = 0) : d119675 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118087, d119675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118087, d119675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118088 q = 0) : d119676 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d118088, d119676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118088, d119676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118089 q = 0) : d119677 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d118089, d119677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118089, d119677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9105 (p : Pattern) (selected : d118095 p = 0) : d119683 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118077 q = 0) : d119665 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118077, d119665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9101 q selected
    | true =>
      simp only [d118077, d119665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118078 q = 0) : d119666 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118078, d119666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118078, d119666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118090 q = 0) : d119678 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118090, d119678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9104 q selected
    | true =>
      simp only [d118090, d119678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118091 q = 0) : d119679 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118091, d119679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118091, d119679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118092 q = 0) : d119680 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118092, d119680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118092, d119680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118093 q = 0) : d119681 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118093, d119681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118093, d119681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118094 q = 0) : d119682 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118094, d119682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118094, d119682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d118095 q = 0) : d119683 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118095, d119683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118095, d119683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9106 (p : Pattern) (selected : d118105 p = 0) : d119628 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118097 q = 0) : d119619 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118097, d119619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118097, d119619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9067 q selected
  have h2 (q : Pattern) (selected : d117911 q = 0) : d119432 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117911, d119432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9067 q selected
    | true =>
      simp only [d117911, d119432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118098 q = 0) : d119620 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118098, d119620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118098, d119620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117912 q = 0) : d119433 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117912, d119433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117912, d119433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118099 q = 0) : d119621 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118099, d119621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118099, d119621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118100 q = 0) : d119622 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118100, d119622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118100, d119622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118101 q = 0) : d119624 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118101, d119624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118101, d119624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9068 q selected
  have h8 (q : Pattern) (selected : d117915 q = 0) : d119436 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117915, d119436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9068 q selected
    | true =>
      simp only [d117915, d119436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d118102 q = 0) : d119625 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118102, d119625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118102, d119625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117916 q = 0) : d119437 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117916, d119437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117916, d119437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d118103 q = 0) : d119626 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118103, d119626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d118103, d119626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d118104 q = 0) : d119627 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118104, d119627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d118104, d119627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d118105 q = 0) : d119628 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118105, d119628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118105, d119628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro9107 (p : Pattern) (selected : d118110 p = 0) : d119645 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118101 q = 0) : d119624 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118101, d119624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118101, d119624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9068 q selected
  have h2 (q : Pattern) (selected : d117915 q = 0) : d119436 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117915, d119436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9068 q selected
    | true =>
      simp only [d117915, d119436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118102 q = 0) : d119625 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118102, d119625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118102, d119625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117916 q = 0) : d119437 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117916, d119437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117916, d119437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118103 q = 0) : d119626 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118103, d119626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118103, d119626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118104 q = 0) : d119627 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118104, d119627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118104, d119627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118106 q = 0) : d119641 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118106, d119641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118106, d119641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9070 q selected
  have h8 (q : Pattern) (selected : d117920 q = 0) : d119441 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117920, d119441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9070 q selected
    | true =>
      simp only [d117920, d119441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d118107 q = 0) : d119642 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118107, d119642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118107, d119642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117921 q = 0) : d119442 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117921, d119442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117921, d119442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d118108 q = 0) : d119643 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118108, d119643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d118108, d119643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d118109 q = 0) : d119644 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118109, d119644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d118109, d119644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d118110 q = 0) : d119645 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118110, d119645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118110, d119645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro9108 (p : Pattern) (selected : d118118 p = 0) : d119653 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118114 q = 0) : d119649 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118114, d119649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118114, d119649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9072 q selected
  have h2 (q : Pattern) (selected : d117928 q = 0) : d119449 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117928, d119449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9072 q selected
    | true =>
      simp only [d117928, d119449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118115 q = 0) : d119650 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118115, d119650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118115, d119650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117929 q = 0) : d119450 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117929, d119450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117929, d119450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118116 q = 0) : d119651 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118116, d119651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118116, d119651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118117 q = 0) : d119652 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118117, d119652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118117, d119652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118118 q = 0) : d119653 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118118, d119653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118118, d119653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro9109 (p : Pattern) (selected : d118123 p = 0) : d119671 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118106 q = 0) : d119641 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118106, d119641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118106, d119641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9070 q selected
  have h2 (q : Pattern) (selected : d117920 q = 0) : d119441 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117920, d119441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9070 q selected
    | true =>
      simp only [d117920, d119441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118107 q = 0) : d119642 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118107, d119642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118107, d119642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117921 q = 0) : d119442 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117921, d119442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117921, d119442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118108 q = 0) : d119643 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118108, d119643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118108, d119643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118109 q = 0) : d119644 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118109, d119644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118109, d119644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118123 q = 0) : d119671 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118123, d119671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118123, d119671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro9110 (p : Pattern) (selected : d118129 p = 0) : d119686 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118111 q = 0) : d119646 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118111, d119646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9106 q selected
    | true =>
      simp only [d118111, d119646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9107 q selected
  have h2 (q : Pattern) (selected : d118112 q = 0) : d119647 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118112, d119647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118112, d119647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118113 q = 0) : d119648 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118113, d119648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118113, d119648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118119 q = 0) : d119654 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118119, d119654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9107 q selected
    | true =>
      simp only [d118119, d119654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9108 q selected
  have h5 (q : Pattern) (selected : d118120 q = 0) : d119655 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118120, d119655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118120, d119655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118121 q = 0) : d119656 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118121, d119656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118121, d119656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d118122 q = 0) : d119657 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118122, d119657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118122, d119657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118124 q = 0) : d119672 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118124, d119672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9107 q selected
    | true =>
      simp only [d118124, d119672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9109 q selected
  have h9 (q : Pattern) (selected : d118125 q = 0) : d119673 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118125, d119673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118125, d119673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d118126 q = 0) : d119674 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118126, d119674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118126, d119674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d118127 q = 0) : d119675 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118127, d119675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d118127, d119675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d118128 q = 0) : d119685 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d118128, d119685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118128, d119685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d118129 q = 0) : d119686 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d118129, d119686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d118129, d119686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro9111 (p : Pattern) (selected : d118133 p = 0) : d119677 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118124 q = 0) : d119672 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118124, d119672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9107 q selected
    | true =>
      simp only [d118124, d119672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9109 q selected
  have h2 (q : Pattern) (selected : d118125 q = 0) : d119673 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118125, d119673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118125, d119673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118126 q = 0) : d119674 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118126, d119674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118126, d119674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118127 q = 0) : d119675 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118127, d119675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118127, d119675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118132 q = 0) : d119676 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d118132, d119676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118132, d119676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118133 q = 0) : d119677 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d118133, d119677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118133, d119677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9112 (p : Pattern) (selected : d118139 p = 0) : d119692 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118130 q = 0) : d119687 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118130, d119687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9110 q selected
    | true =>
      simp only [d118130, d119687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118131 q = 0) : d119688 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118131, d119688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118131, d119688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118134 q = 0) : d119678 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118134, d119678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9111 q selected
    | true =>
      simp only [d118134, d119678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118135 q = 0) : d119679 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118135, d119679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118135, d119679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118136 q = 0) : d119689 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118136, d119689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118136, d119689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118137 q = 0) : d119690 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118137, d119690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118137, d119690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118138 q = 0) : d119691 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118138, d119691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118138, d119691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d118139 q = 0) : d119692 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118139, d119692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118139, d119692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9113 (p : Pattern) (selected : d118143 p = 0) : d119696 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118134 q = 0) : d119678 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118134, d119678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9111 q selected
    | true =>
      simp only [d118134, d119678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118135 q = 0) : d119679 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118135, d119679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118135, d119679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118140 q = 0) : d119693 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118140, d119693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118140, d119693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118141 q = 0) : d119694 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118141, d119694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118141, d119694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118142 q = 0) : d119695 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118142, d119695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118142, d119695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118143 q = 0) : d119696 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118143, d119696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118143, d119696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9114 (p : Pattern) (selected : d118147 p = 0) : d119686 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118058 q = 0) : d119646 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118058, d119646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9096 q selected
    | true =>
      simp only [d118058, d119646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9098 q selected
  have h2 (q : Pattern) (selected : d118059 q = 0) : d119647 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118059, d119647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118059, d119647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118060 q = 0) : d119648 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118060, d119648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118060, d119648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118066 q = 0) : d119654 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118066, d119654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9098 q selected
    | true =>
      simp only [d118066, d119654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9099 q selected
  have h5 (q : Pattern) (selected : d118067 q = 0) : d119655 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118067, d119655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118067, d119655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118068 q = 0) : d119656 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118068, d119656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118068, d119656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d118069 q = 0) : d119657 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118069, d119657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118069, d119657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118084 q = 0) : d119672 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118084, d119672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9098 q selected
    | true =>
      simp only [d118084, d119672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9103 q selected
  have h9 (q : Pattern) (selected : d118085 q = 0) : d119673 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118085, d119673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118085, d119673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d118086 q = 0) : d119674 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118086, d119674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118086, d119674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d118087 q = 0) : d119675 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118087, d119675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d118087, d119675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d118146 q = 0) : d119685 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d118146, d119685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118146, d119685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d118147 q = 0) : d119686 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d118147, d119686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d118147, d119686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro9115 (p : Pattern) (selected : d118153 p = 0) : d119702 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118148 q = 0) : d119687 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118148, d119687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9114 q selected
    | true =>
      simp only [d118148, d119687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118149 q = 0) : d119688 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118149, d119688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118149, d119688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118150 q = 0) : d119699 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118150, d119699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118150, d119699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118151 q = 0) : d119700 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118151, d119700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118151, d119700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118152 q = 0) : d119701 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118152, d119701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118152, d119701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118153 q = 0) : d119702 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118153, d119702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118153, d119702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9116 (p : Pattern) (selected : d118159 p = 0) : d119708 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118096 q = 0) : d119684 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118096, d119684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9102 q selected
    | true =>
      simp only [d118096, d119684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9105 q selected
  have h2 (q : Pattern) (selected : d118144 q = 0) : d119697 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118144, d119697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9112 q selected
    | true =>
      simp only [d118144, d119697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9113 q selected
  have h3 (q : Pattern) (selected : d118145 q = 0) : d119698 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118145, d119698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118145, d119698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118154 q = 0) : d119703 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118154, d119703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9115 q selected
    | true =>
      simp only [d118154, d119703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118155 q = 0) : d119704 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118155, d119704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118155, d119704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118156 q = 0) : d119705 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118156, d119705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118156, d119705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d118157 q = 0) : d119706 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118157, d119706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118157, d119706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118158 q = 0) : d119707 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118158, d119707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118158, d119707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d118159 q = 0) : d119708 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118159, d119708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118159, d119708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro9117 (p : Pattern) (selected : d118164 p = 0) : d119696 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118090 q = 0) : d119678 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118090, d119678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9104 q selected
    | true =>
      simp only [d118090, d119678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118091 q = 0) : d119679 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118091, d119679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118091, d119679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118161 q = 0) : d119693 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118161, d119693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118161, d119693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118162 q = 0) : d119694 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118162, d119694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118162, d119694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118163 q = 0) : d119695 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118163, d119695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118163, d119695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118164 q = 0) : d119696 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118164, d119696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118164, d119696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9118 (p : Pattern) (selected : d118170 p = 0) : d119715 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118165 q = 0) : d119710 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118165, d119710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9117 q selected
    | true =>
      simp only [d118165, d119710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118166 q = 0) : d119711 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118166, d119711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118166, d119711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118167 q = 0) : d119712 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118167, d119712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118167, d119712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118168 q = 0) : d119713 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118168, d119713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118168, d119713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118169 q = 0) : d119714 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118169, d119714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118169, d119714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118170 q = 0) : d119715 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118170, d119715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118170, d119715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9119 (p : Pattern) (selected : d118176 p = 0) : d119721 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117846 q = 0) : d119485 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d117846, d119485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117846, d119485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9051 q selected
  have h2 (q : Pattern) (selected : d117847 q = 0) : d119486 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d117847, d119486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117847, d119486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117856 q = 0) : d119495 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d117856, d119495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9051 q selected
    | true =>
      simp only [d117856, d119495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9054 q selected
  have h4 (q : Pattern) (selected : d117857 q = 0) : d119496 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d117857, d119496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117857, d119496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117858 q = 0) : d119497 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d117858, d119497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117858, d119497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117995 q = 0) : d119583 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d117995, d119583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9080 q selected
    | true =>
      simp only [d117995, d119583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9090 q selected
  have h7 (q : Pattern) (selected : d118013 q = 0) : d119601 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118013, d119601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9091 q selected
    | true =>
      simp only [d118013, d119601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9092 q selected
  have h8 (q : Pattern) (selected : d118014 q = 0) : d119602 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118014, d119602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118014, d119602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d118015 q = 0) : d119603 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d118015, d119603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d118015, d119603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d118016 q = 0) : d119604 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d118016, d119604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118016, d119604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d118020 q = 0) : d119608 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118020, d119608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118020, d119608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9093 q selected
  have h12 (q : Pattern) (selected : d118022 q = 0) : d119610 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118022, d119610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118022, d119610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9094 q selected
  have h13 (q : Pattern) (selected : d118023 q = 0) : d119611 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118023, d119611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d118023, d119611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d118024 q = 0) : d119612 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d118024, d119612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d118024, d119612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d118025 q = 0) : d119613 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d118025, d119613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d118025, d119613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d118026 q = 0) : d119614 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d118026, d119614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d118026, d119614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d118160 q = 0) : d119709 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118160, d119709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118160, d119709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9116 q selected
  have h18 (q : Pattern) (selected : d118171 q = 0) : d119716 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118171, d119716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118171, d119716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9118 q selected
  have h19 (q : Pattern) (selected : d118172 q = 0) : d119717 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118172, d119717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d118172, d119717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d118173 q = 0) : d119718 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d118173, d119718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d118173, d119718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d118174 q = 0) : d119719 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d118174, d119719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d118174, d119719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d118175 q = 0) : d119720 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d118175, d119720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d118175, d119720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d118176 q = 0) : d119721 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d118176, d119721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d118176, d119721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro9120 (p : Pattern) (selected : d118182 p = 0) : d119727 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118177 q = 0) : d119722 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d118177, d119722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118177, d119722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9119 q selected
  have h2 (q : Pattern) (selected : d118178 q = 0) : d119723 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d118178, d119723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118178, d119723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118179 q = 0) : d119724 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d118179, d119724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118179, d119724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118180 q = 0) : d119725 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d118180, d119725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118180, d119725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118181 q = 0) : d119726 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d118181, d119726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118181, d119726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118182 q = 0) : d119727 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d118182, d119727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118182, d119727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9121 (p : Pattern) (selected : d2033 p = 0) : d53312 p = 1 := by
  have h0 (q : Pattern) (selected : d2004 q = 0) : d53283 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2004, d53283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro546 q selected
    | true =>
      simp only [d2004, d53283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro547 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d2008 q = 0) : d53287 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2008, d53287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2008, d53287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro548 q selected
  have h3 (q : Pattern) (selected : d2009 q = 0) : d53288 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2009, d53288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2009, d53288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2020 q = 0) : d53299 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro549 q selected
    | true =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro550 q selected
  have h5 (q : Pattern) (selected : d2024 q = 0) : d53303 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro551 q selected
  have h6 (q : Pattern) (selected : d2025 q = 0) : d53304 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2026 q = 0) : d53305 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2026, d53305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2026, d53305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d2029 q = 0) : d53308 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro552 q selected
    | true =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d2030 q = 0) : d53309 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d2031 q = 0) : d53310 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2031, d53310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2031, d53310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d2032 q = 0) : d53311 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2032, d53311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2032, d53311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d2033 q = 0) : d53312 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2033, d53312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d2033, d53312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h12 p selected
theorem eqIntro9122 (p : Pattern) (selected : d2051 p = 0) : d53330 p = 1 := by
  have h0 (q : Pattern) (selected : d2020 q = 0) : d53299 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro549 q selected
    | true =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro550 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d2024 q = 0) : d53303 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro551 q selected
  have h3 (q : Pattern) (selected : d2025 q = 0) : d53304 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2041 q = 0) : d53320 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2041, d53320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro554 q selected
    | true =>
      simp only [d2041, d53320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro555 q selected
  have h5 (q : Pattern) (selected : d2043 q = 0) : d53322 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro556 q selected
  have h6 (q : Pattern) (selected : d2044 q = 0) : d53323 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2044, d53323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2044, d53323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2045 q = 0) : d53324 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2045, d53324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2045, d53324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d2029 q = 0) : d53308 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro552 q selected
    | true =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d2030 q = 0) : d53309 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d2047 q = 0) : d53326 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro557 q selected
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h11 (q : Pattern) (selected : d2048 q = 0) : d53327 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h12 (q : Pattern) (selected : d2049 q = 0) : d53328 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2049, d53328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d2049, d53328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d2050 q = 0) : d53329 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2050, d53329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2050, d53329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d2051 q = 0) : d53330 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2051, d53330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d2051, d53330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h14 p selected
theorem eqIntro9123 (p : Pattern) (selected : d118195 p = 0) : d119740 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118187 q = 0) : d119732 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118187, d119732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9121 q selected
    | true =>
      simp only [d118187, d119732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118188 q = 0) : d119733 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118188, d119733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118188, d119733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118189 q = 0) : d119734 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118189, d119734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118189, d119734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118190 q = 0) : d119735 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118190, d119735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118190, d119735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118191 q = 0) : d119736 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118191, d119736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9122 q selected
    | true =>
      simp only [d118191, d119736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118192 q = 0) : d119737 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118192, d119737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118192, d119737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118193 q = 0) : d119738 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118193, d119738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118193, d119738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118194 q = 0) : d119739 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118194, d119739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118194, d119739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d118195 q = 0) : d119740 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118195, d119740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118195, d119740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro9124 (p : Pattern) (selected : d2063 p = 0) : d53342 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2058 q = 0) : d53337 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2058, d53337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2058, d53337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro555 q selected
  have h2 (q : Pattern) (selected : d2043 q = 0) : d53322 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro556 q selected
  have h3 (q : Pattern) (selected : d2059 q = 0) : d53338 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2059, d53338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2059, d53338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2047 q = 0) : d53326 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro557 q selected
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2048 q = 0) : d53327 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2060 q = 0) : d53339 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2060, d53339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2060, d53339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2061 q = 0) : d53340 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2061, d53340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2061, d53340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d2062 q = 0) : d53341 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2062, d53341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2062, d53341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d2063 q = 0) : d53342 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2063, d53342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d2063, d53342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro9125 (p : Pattern) (selected : d118200 p = 0) : d119745 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118191 q = 0) : d119736 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118191, d119736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9122 q selected
    | true =>
      simp only [d118191, d119736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118192 q = 0) : d119737 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118192, d119737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118192, d119737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118193 q = 0) : d119738 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118193, d119738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118193, d119738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118194 q = 0) : d119739 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118194, d119739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118194, d119739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118196 q = 0) : d119741 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118196, d119741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9124 q selected
    | true =>
      simp only [d118196, d119741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118197 q = 0) : d119742 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118197, d119742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118197, d119742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118198 q = 0) : d119743 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118198, d119743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118198, d119743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118199 q = 0) : d119744 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118199, d119744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118199, d119744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d118200 q = 0) : d119745 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118200, d119745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118200, d119745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro9126 (p : Pattern) (selected : d5245 p = 0) : d69329 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d5238 q = 0) : d69322 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro557 q selected
  have h2 (q : Pattern) (selected : d5239 q = 0) : d69323 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5239, d69323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d5239, d69323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2047 q = 0) : d53326 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro557 q selected
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2048 q = 0) : d53327 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d5243 q = 0) : d69327 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5243, d69327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d5243, d69327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2061 q = 0) : d53340 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2061, d53340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2061, d53340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d5244 q = 0) : d69328 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5244, d69328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d5244, d69328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d5245 q = 0) : d69329 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5245, d69329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d5245, d69329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9127 (p : Pattern) (selected : d118208 p = 0) : d119753 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118204 q = 0) : d119749 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118204, d119749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9126 q selected
    | true =>
      simp only [d118204, d119749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118205 q = 0) : d119750 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118205, d119750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118205, d119750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118206 q = 0) : d119751 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118206, d119751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118206, d119751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118207 q = 0) : d119752 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118207, d119752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118207, d119752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118208 q = 0) : d119753 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118208, d119753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118208, d119753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro9128 (p : Pattern) (selected : d118213 p = 0) : d119758 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118196 q = 0) : d119741 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118196, d119741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9124 q selected
    | true =>
      simp only [d118196, d119741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118197 q = 0) : d119742 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118197, d119742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118197, d119742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118198 q = 0) : d119743 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118198, d119743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118198, d119743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118199 q = 0) : d119744 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118199, d119744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118199, d119744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118213 q = 0) : d119758 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118213, d119758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118213, d119758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro9129 (p : Pattern) (selected : d118219 p = 0) : d119764 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118201 q = 0) : d119746 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118201, d119746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9123 q selected
    | true =>
      simp only [d118201, d119746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9125 q selected
  have h2 (q : Pattern) (selected : d118202 q = 0) : d119747 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118202, d119747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118202, d119747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118203 q = 0) : d119748 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118203, d119748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118203, d119748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118209 q = 0) : d119754 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118209, d119754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9125 q selected
    | true =>
      simp only [d118209, d119754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9127 q selected
  have h5 (q : Pattern) (selected : d118210 q = 0) : d119755 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118210, d119755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118210, d119755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118211 q = 0) : d119756 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118211, d119756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118211, d119756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d118212 q = 0) : d119757 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118212, d119757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118212, d119757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118214 q = 0) : d119759 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118214, d119759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9125 q selected
    | true =>
      simp only [d118214, d119759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9128 q selected
  have h9 (q : Pattern) (selected : d118215 q = 0) : d119760 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118215, d119760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118215, d119760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d118216 q = 0) : d119761 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118216, d119761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118216, d119761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d118217 q = 0) : d119762 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118217, d119762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d118217, d119762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d118218 q = 0) : d119763 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d118218, d119763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118218, d119763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d118219 q = 0) : d119764 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d118219, d119764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d118219, d119764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro9130 (p : Pattern) (selected : d118223 p = 0) : d119768 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118214 q = 0) : d119759 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118214, d119759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9125 q selected
    | true =>
      simp only [d118214, d119759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9128 q selected
  have h2 (q : Pattern) (selected : d118215 q = 0) : d119760 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118215, d119760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118215, d119760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118216 q = 0) : d119761 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118216, d119761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118216, d119761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118217 q = 0) : d119762 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118217, d119762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118217, d119762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118222 q = 0) : d119767 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d118222, d119767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118222, d119767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118223 q = 0) : d119768 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d118223, d119768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118223, d119768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9131 (p : Pattern) (selected : d118229 p = 0) : d119774 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118220 q = 0) : d119765 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118220, d119765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9129 q selected
    | true =>
      simp only [d118220, d119765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118221 q = 0) : d119766 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118221, d119766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118221, d119766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118224 q = 0) : d119769 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118224, d119769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9130 q selected
    | true =>
      simp only [d118224, d119769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118225 q = 0) : d119770 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118225, d119770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118225, d119770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118226 q = 0) : d119771 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118226, d119771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118226, d119771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118227 q = 0) : d119772 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118227, d119772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118227, d119772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118228 q = 0) : d119773 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118228, d119773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118228, d119773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d118229 q = 0) : d119774 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118229, d119774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118229, d119774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9132 (p : Pattern) (selected : d118233 p = 0) : d119778 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118224 q = 0) : d119769 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118224, d119769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9130 q selected
    | true =>
      simp only [d118224, d119769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118225 q = 0) : d119770 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118225, d119770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118225, d119770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118230 q = 0) : d119775 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118230, d119775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118230, d119775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118231 q = 0) : d119776 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118231, d119776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118231, d119776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118232 q = 0) : d119777 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118232, d119777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118232, d119777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118233 q = 0) : d119778 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118233, d119778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118233, d119778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9133 (p : Pattern) (selected : d118239 p = 0) : d119784 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118234 q = 0) : d119779 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118234, d119779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9131 q selected
    | true =>
      simp only [d118234, d119779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9132 q selected
  have h2 (q : Pattern) (selected : d118235 q = 0) : d119780 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118235, d119780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118235, d119780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118236 q = 0) : d119781 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118236, d119781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118236, d119781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118237 q = 0) : d119782 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118237, d119782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118237, d119782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118238 q = 0) : d119783 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118238, d119783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118238, d119783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118239 q = 0) : d119784 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118239, d119784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118239, d119784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9134 (p : Pattern) (selected : d118242 p = 0) : d119787 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118220 q = 0) : d119765 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118220, d119765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9129 q selected
    | true =>
      simp only [d118220, d119765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118221 q = 0) : d119766 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118221, d119766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118221, d119766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118224 q = 0) : d119769 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118224, d119769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9130 q selected
    | true =>
      simp only [d118224, d119769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118225 q = 0) : d119770 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118225, d119770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118225, d119770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118226 q = 0) : d119771 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118226, d119771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118226, d119771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118227 q = 0) : d119772 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118227, d119772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118227, d119772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118228 q = 0) : d119773 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118228, d119773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118228, d119773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d118242 q = 0) : d119787 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118242, d119787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118242, d119787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9135 (p : Pattern) (selected : d118243 p = 0) : d119788 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118224 q = 0) : d119769 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118224, d119769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9130 q selected
    | true =>
      simp only [d118224, d119769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118225 q = 0) : d119770 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118225, d119770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118225, d119770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118230 q = 0) : d119775 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118230, d119775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118230, d119775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118231 q = 0) : d119776 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118231, d119776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118231, d119776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118232 q = 0) : d119777 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118232, d119777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118232, d119777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118243 q = 0) : d119788 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118243, d119788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118243, d119788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9136 (p : Pattern) (selected : d118249 p = 0) : d119794 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118234 q = 0) : d119779 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118234, d119779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9131 q selected
    | true =>
      simp only [d118234, d119779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9132 q selected
  have h2 (q : Pattern) (selected : d118235 q = 0) : d119780 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118235, d119780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118235, d119780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118236 q = 0) : d119781 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118236, d119781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118236, d119781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118237 q = 0) : d119782 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118237, d119782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118237, d119782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118238 q = 0) : d119783 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118238, d119783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118238, d119783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118244 q = 0) : d119789 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118244, d119789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9134 q selected
    | true =>
      simp only [d118244, d119789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9135 q selected
  have h7 (q : Pattern) (selected : d118245 q = 0) : d119790 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118245, d119790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118245, d119790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118246 q = 0) : d119791 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118246, d119791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118246, d119791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d118247 q = 0) : d119792 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118247, d119792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118247, d119792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d118248 q = 0) : d119793 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118248, d119793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118248, d119793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d118249 q = 0) : d119794 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118249, d119794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118249, d119794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro9137 (p : Pattern) (selected : d118254 p = 0) : d119799 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118220 q = 0) : d119765 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118220, d119765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9129 q selected
    | true =>
      simp only [d118220, d119765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118221 q = 0) : d119766 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118221, d119766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118221, d119766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118224 q = 0) : d119769 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118224, d119769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9130 q selected
    | true =>
      simp only [d118224, d119769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118225 q = 0) : d119770 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118225, d119770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118225, d119770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118226 q = 0) : d119771 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118226, d119771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118226, d119771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118227 q = 0) : d119772 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118227, d119772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118227, d119772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118253 q = 0) : d119798 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118253, d119798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118253, d119798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118254 q = 0) : d119799 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118254, d119799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118254, d119799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9138 (p : Pattern) (selected : d118256 p = 0) : d119801 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118224 q = 0) : d119769 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118224, d119769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9130 q selected
    | true =>
      simp only [d118224, d119769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118225 q = 0) : d119770 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118225, d119770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118225, d119770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118230 q = 0) : d119775 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118230, d119775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118230, d119775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118231 q = 0) : d119776 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118231, d119776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118231, d119776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118255 q = 0) : d119800 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118255, d119800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118255, d119800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118256 q = 0) : d119801 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118256, d119801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118256, d119801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9139 (p : Pattern) (selected : d118263 p = 0) : d119808 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118220 q = 0) : d119765 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118220, d119765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9129 q selected
    | true =>
      simp only [d118220, d119765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118221 q = 0) : d119766 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118221, d119766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118221, d119766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118224 q = 0) : d119769 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118224, d119769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9130 q selected
    | true =>
      simp only [d118224, d119769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118225 q = 0) : d119770 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118225, d119770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118225, d119770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118226 q = 0) : d119771 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118226, d119771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118226, d119771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118261 q = 0) : d119806 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118261, d119806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118261, d119806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d118262 q = 0) : d119807 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118262, d119807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118262, d119807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d118263 q = 0) : d119808 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118263, d119808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118263, d119808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9140 (p : Pattern) (selected : d118266 p = 0) : d119811 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118224 q = 0) : d119769 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118224, d119769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9130 q selected
    | true =>
      simp only [d118224, d119769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118225 q = 0) : d119770 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118225, d119770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118225, d119770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118230 q = 0) : d119775 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118230, d119775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118230, d119775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118264 q = 0) : d119809 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118264, d119809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118264, d119809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118265 q = 0) : d119810 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118265, d119810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118265, d119810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118266 q = 0) : d119811 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118266, d119811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118266, d119811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9141 (p : Pattern) (selected : d2012 p = 0) : d53291 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2004 q = 0) : d53283 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2004, d53283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro546 q selected
    | true =>
      simp only [d2004, d53283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro547 q selected
  have h2 (q : Pattern) (selected : d2008 q = 0) : d53287 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2008, d53287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2008, d53287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro548 q selected
  have h3 (q : Pattern) (selected : d2009 q = 0) : d53288 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2009, d53288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2009, d53288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2010 q = 0) : d53289 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2010, d53289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2010, d53289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2011 q = 0) : d53290 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2011, d53290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2011, d53290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2012 q = 0) : d53291 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2012, d53291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2012, d53291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9142 (p : Pattern) (selected : d118274 p = 0) : d119819 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118270 q = 0) : d119815 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118270, d119815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9141 q selected
    | true =>
      simp only [d118270, d119815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118271 q = 0) : d119816 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118271, d119816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118271, d119816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118272 q = 0) : d119817 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118272, d119817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118272, d119817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118273 q = 0) : d119818 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118273, d119818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118273, d119818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118187 q = 0) : d119732 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118187, d119732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9121 q selected
    | true =>
      simp only [d118187, d119732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118188 q = 0) : d119733 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118188, d119733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118188, d119733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118189 q = 0) : d119734 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118189, d119734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118189, d119734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118190 q = 0) : d119735 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118190, d119735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118190, d119735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d118274 q = 0) : d119819 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118274, d119819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118274, d119819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro9143 (p : Pattern) (selected : d118283 p = 0) : d119828 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118275 q = 0) : d119820 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118275, d119820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9142 q selected
    | true =>
      simp only [d118275, d119820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9123 q selected
  have h2 (q : Pattern) (selected : d118276 q = 0) : d119821 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118276, d119821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118276, d119821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118277 q = 0) : d119822 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118277, d119822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118277, d119822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118278 q = 0) : d119823 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118278, d119823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9123 q selected
    | true =>
      simp only [d118278, d119823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118279 q = 0) : d119824 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118279, d119824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118279, d119824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118280 q = 0) : d119825 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118280, d119825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118280, d119825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d118281 q = 0) : d119826 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118281, d119826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118281, d119826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118201 q = 0) : d119746 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118201, d119746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9123 q selected
    | true =>
      simp only [d118201, d119746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9125 q selected
  have h9 (q : Pattern) (selected : d118202 q = 0) : d119747 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118202, d119747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118202, d119747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d118203 q = 0) : d119748 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118203, d119748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118203, d119748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d118209 q = 0) : d119754 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118209, d119754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9125 q selected
    | true =>
      simp only [d118209, d119754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9127 q selected
  have h12 (q : Pattern) (selected : d118210 q = 0) : d119755 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118210, d119755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118210, d119755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d118211 q = 0) : d119756 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118211, d119756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118211, d119756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d118212 q = 0) : d119757 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118212, d119757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d118212, d119757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d118282 q = 0) : d119827 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d118282, d119827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118282, d119827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d118283 q = 0) : d119828 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d118283, d119828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d118283, d119828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro9144 (p : Pattern) (selected : d118288 p = 0) : d119833 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118201 q = 0) : d119746 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118201, d119746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9123 q selected
    | true =>
      simp only [d118201, d119746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9125 q selected
  have h2 (q : Pattern) (selected : d118202 q = 0) : d119747 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118202, d119747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118202, d119747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118203 q = 0) : d119748 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118203, d119748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118203, d119748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118209 q = 0) : d119754 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118209, d119754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9125 q selected
    | true =>
      simp only [d118209, d119754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9127 q selected
  have h5 (q : Pattern) (selected : d118210 q = 0) : d119755 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118210, d119755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118210, d119755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118211 q = 0) : d119756 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118211, d119756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118211, d119756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d118212 q = 0) : d119757 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118212, d119757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118212, d119757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118286 q = 0) : d119831 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118286, d119831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118286, d119831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d118287 q = 0) : d119832 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d118287, d119832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118287, d119832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d118288 q = 0) : d119833 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d118288, d119833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d118288, d119833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro9145 (p : Pattern) (selected : d118294 p = 0) : d119839 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118284 q = 0) : d119829 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118284, d119829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9143 q selected
    | true =>
      simp only [d118284, d119829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118285 q = 0) : d119830 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118285, d119830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118285, d119830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118289 q = 0) : d119834 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118289, d119834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9144 q selected
    | true =>
      simp only [d118289, d119834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118290 q = 0) : d119835 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118290, d119835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118290, d119835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118291 q = 0) : d119836 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118291, d119836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118291, d119836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118292 q = 0) : d119837 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118292, d119837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118292, d119837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118293 q = 0) : d119838 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118293, d119838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118293, d119838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d118294 q = 0) : d119839 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118294, d119839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118294, d119839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9146 (p : Pattern) (selected : d118298 p = 0) : d119843 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118289 q = 0) : d119834 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118289, d119834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9144 q selected
    | true =>
      simp only [d118289, d119834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118290 q = 0) : d119835 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118290, d119835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118290, d119835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118224 q = 0) : d119769 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118224, d119769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9130 q selected
    | true =>
      simp only [d118224, d119769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118225 q = 0) : d119770 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118225, d119770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118225, d119770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118295 q = 0) : d119840 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118295, d119840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118295, d119840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118296 q = 0) : d119841 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118296, d119841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118296, d119841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118297 q = 0) : d119842 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118297, d119842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118297, d119842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d118298 q = 0) : d119843 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118298, d119843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118298, d119843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9147 (p : Pattern) (selected : d2199 p = 0) : d53312 p = 1 := by
  have h0 (q : Pattern) (selected : d2170 q = 0) : d53283 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2170, d53283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro580 q selected
    | true =>
      simp only [d2170, d53283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro581 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d2174 q = 0) : d53287 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2174, d53287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2174, d53287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro582 q selected
  have h3 (q : Pattern) (selected : d2175 q = 0) : d53288 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2175, d53288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2175, d53288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2186 q = 0) : d53299 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2186, d53299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro583 q selected
    | true =>
      simp only [d2186, d53299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro584 q selected
  have h5 (q : Pattern) (selected : d2190 q = 0) : d53303 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2190, d53303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2190, d53303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro585 q selected
  have h6 (q : Pattern) (selected : d2191 q = 0) : d53304 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2191, d53304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2191, d53304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2192 q = 0) : d53305 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2192, d53305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2192, d53305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d2195 q = 0) : d53308 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2195, d53308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro586 q selected
    | true =>
      simp only [d2195, d53308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d2196 q = 0) : d53309 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2196, d53309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d2196, d53309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d2197 q = 0) : d53310 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2197, d53310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2197, d53310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d2198 q = 0) : d53311 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2198, d53311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2198, d53311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d2199 q = 0) : d53312 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2199, d53312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d2199, d53312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h12 p selected
theorem eqIntro9148 (p : Pattern) (selected : d2217 p = 0) : d53330 p = 1 := by
  have h0 (q : Pattern) (selected : d2186 q = 0) : d53299 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2186, d53299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro583 q selected
    | true =>
      simp only [d2186, d53299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro584 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d2190 q = 0) : d53303 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2190, d53303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2190, d53303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro585 q selected
  have h3 (q : Pattern) (selected : d2191 q = 0) : d53304 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2191, d53304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2191, d53304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2207 q = 0) : d53320 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2207, d53320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro588 q selected
    | true =>
      simp only [d2207, d53320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro589 q selected
  have h5 (q : Pattern) (selected : d2209 q = 0) : d53322 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2209, d53322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2209, d53322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro590 q selected
  have h6 (q : Pattern) (selected : d2210 q = 0) : d53323 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2210, d53323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2210, d53323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2211 q = 0) : d53324 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2211, d53324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2211, d53324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d2195 q = 0) : d53308 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2195, d53308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro586 q selected
    | true =>
      simp only [d2195, d53308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d2196 q = 0) : d53309 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2196, d53309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d2196, d53309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d2213 q = 0) : d53326 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2213, d53326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro591 q selected
    | true =>
      simp only [d2213, d53326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h11 (q : Pattern) (selected : d2214 q = 0) : d53327 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2214, d53327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d2214, d53327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h12 (q : Pattern) (selected : d2215 q = 0) : d53328 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2215, d53328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d2215, d53328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d2216 q = 0) : d53329 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2216, d53329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2216, d53329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d2217 q = 0) : d53330 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2217, d53330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d2217, d53330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h14 p selected
theorem eqIntro9149 (p : Pattern) (selected : d118308 p = 0) : d119740 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118300 q = 0) : d119732 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118300, d119732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9147 q selected
    | true =>
      simp only [d118300, d119732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118301 q = 0) : d119733 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118301, d119733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118301, d119733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118302 q = 0) : d119734 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118302, d119734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118302, d119734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118303 q = 0) : d119735 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118303, d119735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118303, d119735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118304 q = 0) : d119736 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118304, d119736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9148 q selected
    | true =>
      simp only [d118304, d119736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118305 q = 0) : d119737 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118305, d119737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118305, d119737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118306 q = 0) : d119738 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118306, d119738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118306, d119738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118307 q = 0) : d119739 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118307, d119739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118307, d119739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d118308 q = 0) : d119740 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118308, d119740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118308, d119740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro9150 (p : Pattern) (selected : d2229 p = 0) : d53342 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2224 q = 0) : d53337 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2224, d53337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2224, d53337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro589 q selected
  have h2 (q : Pattern) (selected : d2209 q = 0) : d53322 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2209, d53322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2209, d53322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro590 q selected
  have h3 (q : Pattern) (selected : d2225 q = 0) : d53338 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2225, d53338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2225, d53338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2213 q = 0) : d53326 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2213, d53326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro591 q selected
    | true =>
      simp only [d2213, d53326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2214 q = 0) : d53327 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2214, d53327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2214, d53327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2226 q = 0) : d53339 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2226, d53339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2226, d53339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2227 q = 0) : d53340 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2227, d53340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2227, d53340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d2228 q = 0) : d53341 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2228, d53341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2228, d53341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d2229 q = 0) : d53342 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2229, d53342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d2229, d53342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro9151 (p : Pattern) (selected : d118313 p = 0) : d119745 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118304 q = 0) : d119736 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118304, d119736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9148 q selected
    | true =>
      simp only [d118304, d119736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118305 q = 0) : d119737 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118305, d119737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118305, d119737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118306 q = 0) : d119738 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118306, d119738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118306, d119738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118307 q = 0) : d119739 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118307, d119739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118307, d119739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118309 q = 0) : d119741 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118309, d119741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9150 q selected
    | true =>
      simp only [d118309, d119741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118310 q = 0) : d119742 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118310, d119742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118310, d119742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118311 q = 0) : d119743 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118311, d119743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118311, d119743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118312 q = 0) : d119744 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118312, d119744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118312, d119744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d118313 q = 0) : d119745 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118313, d119745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118313, d119745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro9152 (p : Pattern) (selected : d10480 p = 0) : d69329 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10476 q = 0) : d69322 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10476, d69322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10476, d69322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro591 q selected
  have h2 (q : Pattern) (selected : d10477 q = 0) : d69323 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10477, d69323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10477, d69323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2213 q = 0) : d53326 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2213, d53326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro591 q selected
    | true =>
      simp only [d2213, d53326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2214 q = 0) : d53327 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2214, d53327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2214, d53327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10478 q = 0) : d69327 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10478, d69327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10478, d69327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2227 q = 0) : d53340 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2227, d53340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2227, d53340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10479 q = 0) : d69328 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10479, d69328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10479, d69328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10480 q = 0) : d69329 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10480, d69329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10480, d69329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9153 (p : Pattern) (selected : d118321 p = 0) : d119753 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118317 q = 0) : d119749 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118317, d119749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9152 q selected
    | true =>
      simp only [d118317, d119749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118318 q = 0) : d119750 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118318, d119750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118318, d119750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118319 q = 0) : d119751 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118319, d119751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118319, d119751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118320 q = 0) : d119752 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118320, d119752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118320, d119752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118321 q = 0) : d119753 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118321, d119753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118321, d119753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro9154 (p : Pattern) (selected : d118326 p = 0) : d119758 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118309 q = 0) : d119741 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118309, d119741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9150 q selected
    | true =>
      simp only [d118309, d119741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118310 q = 0) : d119742 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118310, d119742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118310, d119742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118311 q = 0) : d119743 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118311, d119743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118311, d119743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118312 q = 0) : d119744 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118312, d119744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118312, d119744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118326 q = 0) : d119758 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118326, d119758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118326, d119758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro9155 (p : Pattern) (selected : d118332 p = 0) : d119764 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118314 q = 0) : d119746 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118314, d119746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9149 q selected
    | true =>
      simp only [d118314, d119746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9151 q selected
  have h2 (q : Pattern) (selected : d118315 q = 0) : d119747 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118315, d119747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118315, d119747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118316 q = 0) : d119748 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118316, d119748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118316, d119748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118322 q = 0) : d119754 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118322, d119754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9151 q selected
    | true =>
      simp only [d118322, d119754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9153 q selected
  have h5 (q : Pattern) (selected : d118323 q = 0) : d119755 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118323, d119755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118323, d119755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118324 q = 0) : d119756 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118324, d119756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118324, d119756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d118325 q = 0) : d119757 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118325, d119757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118325, d119757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118327 q = 0) : d119759 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118327, d119759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9151 q selected
    | true =>
      simp only [d118327, d119759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9154 q selected
  have h9 (q : Pattern) (selected : d118328 q = 0) : d119760 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118328, d119760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118328, d119760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d118329 q = 0) : d119761 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118329, d119761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118329, d119761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d118330 q = 0) : d119762 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118330, d119762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d118330, d119762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d118331 q = 0) : d119763 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d118331, d119763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118331, d119763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d118332 q = 0) : d119764 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d118332, d119764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d118332, d119764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro9156 (p : Pattern) (selected : d118336 p = 0) : d119768 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118327 q = 0) : d119759 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118327, d119759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9151 q selected
    | true =>
      simp only [d118327, d119759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9154 q selected
  have h2 (q : Pattern) (selected : d118328 q = 0) : d119760 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118328, d119760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118328, d119760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118329 q = 0) : d119761 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118329, d119761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118329, d119761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118330 q = 0) : d119762 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118330, d119762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118330, d119762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118335 q = 0) : d119767 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d118335, d119767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118335, d119767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118336 q = 0) : d119768 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d118336, d119768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118336, d119768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9157 (p : Pattern) (selected : d118342 p = 0) : d119774 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118333 q = 0) : d119765 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118333, d119765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9155 q selected
    | true =>
      simp only [d118333, d119765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118334 q = 0) : d119766 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118334, d119766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118334, d119766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118337 q = 0) : d119769 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118337, d119769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9156 q selected
    | true =>
      simp only [d118337, d119769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118338 q = 0) : d119770 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118338, d119770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118338, d119770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118339 q = 0) : d119771 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118339, d119771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118339, d119771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118340 q = 0) : d119772 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118340, d119772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118340, d119772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118341 q = 0) : d119773 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118341, d119773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118341, d119773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d118342 q = 0) : d119774 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118342, d119774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118342, d119774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9158 (p : Pattern) (selected : d118346 p = 0) : d119778 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118337 q = 0) : d119769 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118337, d119769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9156 q selected
    | true =>
      simp only [d118337, d119769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118338 q = 0) : d119770 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118338, d119770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118338, d119770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118343 q = 0) : d119775 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118343, d119775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118343, d119775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118344 q = 0) : d119776 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118344, d119776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118344, d119776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118345 q = 0) : d119777 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118345, d119777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118345, d119777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118346 q = 0) : d119778 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118346, d119778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118346, d119778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9159 (p : Pattern) (selected : d118352 p = 0) : d119849 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118220 q = 0) : d119765 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118220, d119765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9129 q selected
    | true =>
      simp only [d118220, d119765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118221 q = 0) : d119766 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118221, d119766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118221, d119766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118349 q = 0) : d119846 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118349, d119846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118349, d119846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118350 q = 0) : d119847 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118350, d119847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118350, d119847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118351 q = 0) : d119848 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118351, d119848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118351, d119848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118352 q = 0) : d119849 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118352, d119849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118352, d119849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9160 (p : Pattern) (selected : d118358 p = 0) : d119855 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118257 q = 0) : d119802 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118257, d119802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9137 q selected
    | true =>
      simp only [d118257, d119802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9138 q selected
  have h2 (q : Pattern) (selected : d118258 q = 0) : d119803 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118258, d119803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118258, d119803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118259 q = 0) : d119804 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118259, d119804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118259, d119804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118260 q = 0) : d119805 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118260, d119805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118260, d119805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118267 q = 0) : d119812 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118267, d119812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9139 q selected
    | true =>
      simp only [d118267, d119812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9140 q selected
  have h6 (q : Pattern) (selected : d118268 q = 0) : d119813 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118268, d119813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118268, d119813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d118269 q = 0) : d119814 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118269, d119814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118269, d119814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d118299 q = 0) : d119844 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118299, d119844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9145 q selected
    | true =>
      simp only [d118299, d119844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9146 q selected
  have h9 (q : Pattern) (selected : d118347 q = 0) : d119779 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118347, d119779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9157 q selected
    | true =>
      simp only [d118347, d119779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9158 q selected
  have h10 (q : Pattern) (selected : d118348 q = 0) : d119845 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118348, d119845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d118348, d119845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d118353 q = 0) : d119850 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118353, d119850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9159 q selected
    | true =>
      simp only [d118353, d119850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d118354 q = 0) : d119851 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118354, d119851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d118354, d119851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d118355 q = 0) : d119852 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118355, d119852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d118355, d119852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d118356 q = 0) : d119853 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118356, d119853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118356, d119853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d118357 q = 0) : d119854 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118357, d119854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118357, d119854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d118358 q = 0) : d119855 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118358, d119855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118358, d119855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro9161 (p : Pattern) (selected : d118359 p = 0) : d119856 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118220 q = 0) : d119765 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118220, d119765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9129 q selected
    | true =>
      simp only [d118220, d119765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118221 q = 0) : d119766 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118221, d119766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118221, d119766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118224 q = 0) : d119769 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118224, d119769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9130 q selected
    | true =>
      simp only [d118224, d119769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118225 q = 0) : d119770 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118225, d119770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118225, d119770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118226 q = 0) : d119771 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118226, d119771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118226, d119771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118227 q = 0) : d119772 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118227, d119772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118227, d119772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118253 q = 0) : d119798 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118253, d119798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118253, d119798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118359 q = 0) : d119856 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118359, d119856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118359, d119856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9162 (p : Pattern) (selected : d118360 p = 0) : d119857 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118224 q = 0) : d119769 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118224, d119769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9130 q selected
    | true =>
      simp only [d118224, d119769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118225 q = 0) : d119770 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118225, d119770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118225, d119770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118230 q = 0) : d119775 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118230, d119775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118230, d119775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118231 q = 0) : d119776 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118231, d119776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118231, d119776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118255 q = 0) : d119800 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118255, d119800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118255, d119800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118360 q = 0) : d119857 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118360, d119857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118360, d119857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9163 (p : Pattern) (selected : d118365 p = 0) : d119862 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118220 q = 0) : d119765 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118220, d119765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9129 q selected
    | true =>
      simp only [d118220, d119765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118221 q = 0) : d119766 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118221, d119766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118221, d119766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118224 q = 0) : d119769 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118224, d119769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9130 q selected
    | true =>
      simp only [d118224, d119769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118225 q = 0) : d119770 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118225, d119770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118225, d119770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118226 q = 0) : d119771 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118226, d119771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118226, d119771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118261 q = 0) : d119806 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118261, d119806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118261, d119806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d118262 q = 0) : d119807 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118262, d119807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118262, d119807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d118365 q = 0) : d119862 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118365, d119862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118365, d119862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9164 (p : Pattern) (selected : d118366 p = 0) : d119863 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118224 q = 0) : d119769 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118224, d119769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9130 q selected
    | true =>
      simp only [d118224, d119769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118225 q = 0) : d119770 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118225, d119770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118225, d119770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118230 q = 0) : d119775 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118230, d119775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118230, d119775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118264 q = 0) : d119809 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118264, d119809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118264, d119809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118265 q = 0) : d119810 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118265, d119810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118265, d119810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118366 q = 0) : d119863 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118366, d119863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118366, d119863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9165 (p : Pattern) (selected : d118370 p = 0) : d119867 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118284 q = 0) : d119829 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118284, d119829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9143 q selected
    | true =>
      simp only [d118284, d119829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118285 q = 0) : d119830 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118285, d119830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118285, d119830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118289 q = 0) : d119834 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118289, d119834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9144 q selected
    | true =>
      simp only [d118289, d119834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118290 q = 0) : d119835 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118290, d119835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118290, d119835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118291 q = 0) : d119836 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118291, d119836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118291, d119836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118292 q = 0) : d119837 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118292, d119837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118292, d119837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118293 q = 0) : d119838 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118293, d119838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118293, d119838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d118370 q = 0) : d119867 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118370, d119867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118370, d119867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9166 (p : Pattern) (selected : d118371 p = 0) : d119868 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118289 q = 0) : d119834 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118289, d119834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9144 q selected
    | true =>
      simp only [d118289, d119834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118290 q = 0) : d119835 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118290, d119835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118290, d119835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118224 q = 0) : d119769 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118224, d119769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9130 q selected
    | true =>
      simp only [d118224, d119769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118225 q = 0) : d119770 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118225, d119770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118225, d119770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118295 q = 0) : d119840 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118295, d119840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118295, d119840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118296 q = 0) : d119841 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118296, d119841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118296, d119841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118297 q = 0) : d119842 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118297, d119842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118297, d119842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d118371 q = 0) : d119868 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118371, d119868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118371, d119868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9167 (p : Pattern) (selected : d118373 p = 0) : d119787 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118333 q = 0) : d119765 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118333, d119765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9155 q selected
    | true =>
      simp only [d118333, d119765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118334 q = 0) : d119766 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118334, d119766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118334, d119766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118337 q = 0) : d119769 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118337, d119769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9156 q selected
    | true =>
      simp only [d118337, d119769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118338 q = 0) : d119770 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118338, d119770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118338, d119770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118339 q = 0) : d119771 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118339, d119771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118339, d119771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118340 q = 0) : d119772 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118340, d119772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118340, d119772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118341 q = 0) : d119773 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118341, d119773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118341, d119773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d118373 q = 0) : d119787 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118373, d119787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118373, d119787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9168 (p : Pattern) (selected : d118374 p = 0) : d119788 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118337 q = 0) : d119769 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118337, d119769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9156 q selected
    | true =>
      simp only [d118337, d119769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118338 q = 0) : d119770 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118338, d119770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118338, d119770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118343 q = 0) : d119775 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118343, d119775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118343, d119775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118344 q = 0) : d119776 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118344, d119776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118344, d119776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118345 q = 0) : d119777 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118345, d119777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118345, d119777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118374 q = 0) : d119788 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118374, d119788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118374, d119788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9169 (p : Pattern) (selected : d118377 p = 0) : d119871 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118220 q = 0) : d119765 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118220, d119765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9129 q selected
    | true =>
      simp only [d118220, d119765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118221 q = 0) : d119766 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118221, d119766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118221, d119766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118349 q = 0) : d119846 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118349, d119846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118349, d119846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118350 q = 0) : d119847 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118350, d119847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118350, d119847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118351 q = 0) : d119848 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118351, d119848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118351, d119848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118377 q = 0) : d119871 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118377, d119871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118377, d119871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9170 (p : Pattern) (selected : d118383 p = 0) : d119877 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118257 q = 0) : d119802 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118257, d119802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9137 q selected
    | true =>
      simp only [d118257, d119802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9138 q selected
  have h2 (q : Pattern) (selected : d118258 q = 0) : d119803 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118258, d119803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118258, d119803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118259 q = 0) : d119804 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118259, d119804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118259, d119804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118260 q = 0) : d119805 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118260, d119805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118260, d119805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118267 q = 0) : d119812 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118267, d119812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9139 q selected
    | true =>
      simp only [d118267, d119812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9140 q selected
  have h6 (q : Pattern) (selected : d118268 q = 0) : d119813 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118268, d119813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118268, d119813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d118269 q = 0) : d119814 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118269, d119814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118269, d119814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d118299 q = 0) : d119844 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118299, d119844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9145 q selected
    | true =>
      simp only [d118299, d119844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9146 q selected
  have h9 (q : Pattern) (selected : d118347 q = 0) : d119779 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118347, d119779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9157 q selected
    | true =>
      simp only [d118347, d119779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9158 q selected
  have h10 (q : Pattern) (selected : d118348 q = 0) : d119845 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118348, d119845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d118348, d119845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d118353 q = 0) : d119850 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118353, d119850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9159 q selected
    | true =>
      simp only [d118353, d119850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d118354 q = 0) : d119851 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118354, d119851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d118354, d119851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d118355 q = 0) : d119852 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118355, d119852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d118355, d119852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d118356 q = 0) : d119853 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118356, d119853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118356, d119853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d118357 q = 0) : d119854 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118357, d119854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118357, d119854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d118361 q = 0) : d119858 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118361, d119858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9161 q selected
    | true =>
      simp only [d118361, d119858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9162 q selected
  have h17 (q : Pattern) (selected : d118362 q = 0) : d119859 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118362, d119859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118362, d119859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d118363 q = 0) : d119860 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118363, d119860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d118363, d119860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d118364 q = 0) : d119861 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118364, d119861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118364, d119861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d118367 q = 0) : d119864 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118367, d119864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9163 q selected
    | true =>
      simp only [d118367, d119864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9164 q selected
  have h21 (q : Pattern) (selected : d118368 q = 0) : d119865 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118368, d119865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118368, d119865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d118369 q = 0) : d119866 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118369, d119866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d118369, d119866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d118372 q = 0) : d119869 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118372, d119869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9165 q selected
    | true =>
      simp only [d118372, d119869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9166 q selected
  have h24 (q : Pattern) (selected : d118375 q = 0) : d119789 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118375, d119789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9167 q selected
    | true =>
      simp only [d118375, d119789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9168 q selected
  have h25 (q : Pattern) (selected : d118376 q = 0) : d119870 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118376, d119870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d118376, d119870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d118378 q = 0) : d119872 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118378, d119872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9169 q selected
    | true =>
      simp only [d118378, d119872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d118379 q = 0) : d119873 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118379, d119873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d118379, d119873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d118380 q = 0) : d119874 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118380, d119874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d118380, d119874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d118381 q = 0) : d119875 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118381, d119875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d118381, d119875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d118382 q = 0) : d119876 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118382, d119876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d118382, d119876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d118383 q = 0) : d119877 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118383, d119877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d118383, d119877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro9171 (p : Pattern) (selected : d118395 p = 0) : d119889 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118385 q = 0) : d119879 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118385, d119879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9146 q selected
    | true =>
      simp only [d118385, d119879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9132 q selected
  have h2 (q : Pattern) (selected : d118386 q = 0) : d119880 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118386, d119880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118386, d119880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118387 q = 0) : d119881 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118387, d119881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118387, d119881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118388 q = 0) : d119882 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118388, d119882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118388, d119882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118389 q = 0) : d119883 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118389, d119883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118389, d119883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118390 q = 0) : d119884 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118390, d119884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9132 q selected
    | true =>
      simp only [d118390, d119884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118391 q = 0) : d119885 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118391, d119885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118391, d119885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118392 q = 0) : d119886 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118392, d119886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118392, d119886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d118393 q = 0) : d119887 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118393, d119887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118393, d119887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d118394 q = 0) : d119888 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118394, d119888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118394, d119888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d118395 q = 0) : d119889 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118395, d119889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118395, d119889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro9172 (p : Pattern) (selected : d118401 p = 0) : d119895 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118390 q = 0) : d119884 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118390, d119884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9132 q selected
    | true =>
      simp only [d118390, d119884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118391 q = 0) : d119885 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118391, d119885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118391, d119885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118392 q = 0) : d119886 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118392, d119886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118392, d119886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118393 q = 0) : d119887 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118393, d119887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118393, d119887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118394 q = 0) : d119888 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118394, d119888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118394, d119888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118396 q = 0) : d119890 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118396, d119890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9135 q selected
    | true =>
      simp only [d118396, d119890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118397 q = 0) : d119891 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118397, d119891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118397, d119891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118398 q = 0) : d119892 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118398, d119892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118398, d119892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d118399 q = 0) : d119893 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118399, d119893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118399, d119893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d118400 q = 0) : d119894 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118400, d119894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118400, d119894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d118401 q = 0) : d119895 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118401, d119895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118401, d119895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro9173 (p : Pattern) (selected : d118408 p = 0) : d119902 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118372 q = 0) : d119869 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118372, d119869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9165 q selected
    | true =>
      simp only [d118372, d119869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9166 q selected
  have h2 (q : Pattern) (selected : d118375 q = 0) : d119789 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118375, d119789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9167 q selected
    | true =>
      simp only [d118375, d119789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9168 q selected
  have h3 (q : Pattern) (selected : d118376 q = 0) : d119870 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118376, d119870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118376, d119870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118378 q = 0) : d119872 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118378, d119872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9169 q selected
    | true =>
      simp only [d118378, d119872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118379 q = 0) : d119873 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118379, d119873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118379, d119873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118380 q = 0) : d119874 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118380, d119874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118380, d119874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d118406 q = 0) : d119900 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118406, d119900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118406, d119900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118407 q = 0) : d119901 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118407, d119901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118407, d119901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d118408 q = 0) : d119902 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118408, d119902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118408, d119902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro9174 (p : Pattern) (selected : d118410 p = 0) : d119904 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118396 q = 0) : d119890 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118396, d119890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9135 q selected
    | true =>
      simp only [d118396, d119890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118397 q = 0) : d119891 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118397, d119891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118397, d119891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118398 q = 0) : d119892 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118398, d119892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118398, d119892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118399 q = 0) : d119893 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118399, d119893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118399, d119893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118400 q = 0) : d119894 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118400, d119894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118400, d119894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118410 q = 0) : d119904 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118410, d119904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118410, d119904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9175 (p : Pattern) (selected : d118424 p = 0) : d119918 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118416 q = 0) : d119910 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118416, d119910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118416, d119910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9141 q selected
  have h2 (q : Pattern) (selected : d118270 q = 0) : d119815 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118270, d119815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9141 q selected
    | true =>
      simp only [d118270, d119815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118417 q = 0) : d119911 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118417, d119911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118417, d119911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118271 q = 0) : d119816 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118271, d119816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118271, d119816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118418 q = 0) : d119912 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118418, d119912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118418, d119912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118419 q = 0) : d119913 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118419, d119913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118419, d119913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118420 q = 0) : d119914 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118420, d119914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118420, d119914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9121 q selected
  have h8 (q : Pattern) (selected : d118187 q = 0) : d119732 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118187, d119732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9121 q selected
    | true =>
      simp only [d118187, d119732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d118421 q = 0) : d119915 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118421, d119915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118421, d119915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d118188 q = 0) : d119733 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118188, d119733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d118188, d119733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d118422 q = 0) : d119916 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118422, d119916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d118422, d119916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d118423 q = 0) : d119917 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118423, d119917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d118423, d119917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d118424 q = 0) : d119918 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118424, d119918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118424, d119918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro9176 (p : Pattern) (selected : d118429 p = 0) : d119923 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118420 q = 0) : d119914 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118420, d119914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118420, d119914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9121 q selected
  have h2 (q : Pattern) (selected : d118187 q = 0) : d119732 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118187, d119732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9121 q selected
    | true =>
      simp only [d118187, d119732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118421 q = 0) : d119915 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118421, d119915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118421, d119915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118188 q = 0) : d119733 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118188, d119733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118188, d119733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118422 q = 0) : d119916 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118422, d119916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118422, d119916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118423 q = 0) : d119917 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118423, d119917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118423, d119917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118425 q = 0) : d119919 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118425, d119919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118425, d119919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9122 q selected
  have h8 (q : Pattern) (selected : d118191 q = 0) : d119736 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118191, d119736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9122 q selected
    | true =>
      simp only [d118191, d119736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d118426 q = 0) : d119920 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118426, d119920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118426, d119920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d118192 q = 0) : d119737 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118192, d119737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d118192, d119737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d118427 q = 0) : d119921 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118427, d119921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d118427, d119921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d118428 q = 0) : d119922 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118428, d119922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d118428, d119922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d118429 q = 0) : d119923 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118429, d119923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118429, d119923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro9177 (p : Pattern) (selected : d118441 p = 0) : d119935 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118425 q = 0) : d119919 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118425, d119919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118425, d119919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9122 q selected
  have h2 (q : Pattern) (selected : d118191 q = 0) : d119736 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118191, d119736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9122 q selected
    | true =>
      simp only [d118191, d119736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118426 q = 0) : d119920 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118426, d119920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118426, d119920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118192 q = 0) : d119737 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118192, d119737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118192, d119737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118427 q = 0) : d119921 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118427, d119921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118427, d119921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118428 q = 0) : d119922 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118428, d119922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118428, d119922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118437 q = 0) : d119931 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118437, d119931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118437, d119931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9124 q selected
  have h8 (q : Pattern) (selected : d118196 q = 0) : d119741 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118196, d119741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9124 q selected
    | true =>
      simp only [d118196, d119741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d118438 q = 0) : d119932 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118438, d119932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118438, d119932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d118197 q = 0) : d119742 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118197, d119742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d118197, d119742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d118439 q = 0) : d119933 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118439, d119933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d118439, d119933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d118440 q = 0) : d119934 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118440, d119934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d118440, d119934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d118441 q = 0) : d119935 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118441, d119935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118441, d119935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro9178 (p : Pattern) (selected : d118449 p = 0) : d119943 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118445 q = 0) : d119939 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118445, d119939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118445, d119939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9126 q selected
  have h2 (q : Pattern) (selected : d118204 q = 0) : d119749 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118204, d119749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9126 q selected
    | true =>
      simp only [d118204, d119749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118446 q = 0) : d119940 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118446, d119940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118446, d119940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118205 q = 0) : d119750 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118205, d119750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118205, d119750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118447 q = 0) : d119941 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118447, d119941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118447, d119941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118448 q = 0) : d119942 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118448, d119942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118448, d119942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118449 q = 0) : d119943 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118449, d119943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118449, d119943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro9179 (p : Pattern) (selected : d118455 p = 0) : d119949 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118430 q = 0) : d119924 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118430, d119924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9175 q selected
    | true =>
      simp only [d118430, d119924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9176 q selected
  have h2 (q : Pattern) (selected : d118431 q = 0) : d119925 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118431, d119925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118431, d119925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118432 q = 0) : d119926 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118432, d119926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118432, d119926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118433 q = 0) : d119927 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118433, d119927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9176 q selected
    | true =>
      simp only [d118433, d119927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118434 q = 0) : d119928 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118434, d119928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118434, d119928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118435 q = 0) : d119929 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118435, d119929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118435, d119929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d118436 q = 0) : d119930 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118436, d119930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118436, d119930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118442 q = 0) : d119936 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118442, d119936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9176 q selected
    | true =>
      simp only [d118442, d119936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9177 q selected
  have h9 (q : Pattern) (selected : d118443 q = 0) : d119937 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118443, d119937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118443, d119937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d118444 q = 0) : d119938 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118444, d119938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118444, d119938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d118450 q = 0) : d119944 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118450, d119944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9177 q selected
    | true =>
      simp only [d118450, d119944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9178 q selected
  have h12 (q : Pattern) (selected : d118451 q = 0) : d119945 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118451, d119945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118451, d119945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d118452 q = 0) : d119946 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118452, d119946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118452, d119946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d118453 q = 0) : d119947 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118453, d119947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d118453, d119947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d118454 q = 0) : d119948 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d118454, d119948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118454, d119948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d118455 q = 0) : d119949 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d118455, d119949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d118455, d119949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro9180 (p : Pattern) (selected : d118460 p = 0) : d119954 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118442 q = 0) : d119936 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118442, d119936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9176 q selected
    | true =>
      simp only [d118442, d119936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9177 q selected
  have h2 (q : Pattern) (selected : d118443 q = 0) : d119937 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118443, d119937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118443, d119937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118444 q = 0) : d119938 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118444, d119938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118444, d119938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118450 q = 0) : d119944 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118450, d119944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9177 q selected
    | true =>
      simp only [d118450, d119944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9178 q selected
  have h5 (q : Pattern) (selected : d118451 q = 0) : d119945 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118451, d119945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118451, d119945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118452 q = 0) : d119946 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118452, d119946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118452, d119946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d118453 q = 0) : d119947 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118453, d119947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118453, d119947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118458 q = 0) : d119952 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118458, d119952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118458, d119952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d118459 q = 0) : d119953 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d118459, d119953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118459, d119953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d118460 q = 0) : d119954 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d118460, d119954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d118460, d119954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro9181 (p : Pattern) (selected : d118466 p = 0) : d119960 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118456 q = 0) : d119950 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118456, d119950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9179 q selected
    | true =>
      simp only [d118456, d119950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118457 q = 0) : d119951 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118457, d119951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118457, d119951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118461 q = 0) : d119955 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118461, d119955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9180 q selected
    | true =>
      simp only [d118461, d119955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118462 q = 0) : d119956 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118462, d119956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118462, d119956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118463 q = 0) : d119957 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118463, d119957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118463, d119957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118464 q = 0) : d119958 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118464, d119958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118464, d119958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118465 q = 0) : d119959 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118465, d119959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118465, d119959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d118466 q = 0) : d119960 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118466, d119960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118466, d119960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9182 (p : Pattern) (selected : d118467 p = 0) : d119961 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118437 q = 0) : d119931 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118437, d119931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118437, d119931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9124 q selected
  have h2 (q : Pattern) (selected : d118196 q = 0) : d119741 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118196, d119741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9124 q selected
    | true =>
      simp only [d118196, d119741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118438 q = 0) : d119932 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118438, d119932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118438, d119932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118197 q = 0) : d119742 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118197, d119742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118197, d119742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118439 q = 0) : d119933 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118439, d119933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118439, d119933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118440 q = 0) : d119934 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118440, d119934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118440, d119934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118467 q = 0) : d119961 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118467, d119961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118467, d119961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro9183 (p : Pattern) (selected : d118473 p = 0) : d119967 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118468 q = 0) : d119962 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118468, d119962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9177 q selected
    | true =>
      simp only [d118468, d119962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9182 q selected
  have h2 (q : Pattern) (selected : d118469 q = 0) : d119963 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118469, d119963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118469, d119963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118470 q = 0) : d119964 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118470, d119964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118470, d119964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118471 q = 0) : d119965 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118471, d119965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118471, d119965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118472 q = 0) : d119966 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d118472, d119966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118472, d119966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118473 q = 0) : d119967 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d118473, d119967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118473, d119967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9184 (p : Pattern) (selected : d118479 p = 0) : d119973 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118461 q = 0) : d119955 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118461, d119955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9180 q selected
    | true =>
      simp only [d118461, d119955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118462 q = 0) : d119956 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118462, d119956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118462, d119956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118474 q = 0) : d119968 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118474, d119968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9183 q selected
    | true =>
      simp only [d118474, d119968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118475 q = 0) : d119969 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118475, d119969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118475, d119969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118476 q = 0) : d119970 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118476, d119970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118476, d119970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118477 q = 0) : d119971 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118477, d119971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118477, d119971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118478 q = 0) : d119972 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118478, d119972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118478, d119972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d118479 q = 0) : d119973 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118479, d119973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118479, d119973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9185 (p : Pattern) (selected : d118489 p = 0) : d119923 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118481 q = 0) : d119914 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118481, d119914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118481, d119914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9147 q selected
  have h2 (q : Pattern) (selected : d118300 q = 0) : d119732 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118300, d119732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9147 q selected
    | true =>
      simp only [d118300, d119732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118482 q = 0) : d119915 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118482, d119915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118482, d119915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118301 q = 0) : d119733 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118301, d119733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118301, d119733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118483 q = 0) : d119916 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118483, d119916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118483, d119916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118484 q = 0) : d119917 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118484, d119917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118484, d119917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118485 q = 0) : d119919 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118485, d119919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118485, d119919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9148 q selected
  have h8 (q : Pattern) (selected : d118304 q = 0) : d119736 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118304, d119736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9148 q selected
    | true =>
      simp only [d118304, d119736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d118486 q = 0) : d119920 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118486, d119920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118486, d119920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d118305 q = 0) : d119737 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118305, d119737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d118305, d119737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d118487 q = 0) : d119921 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118487, d119921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d118487, d119921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d118488 q = 0) : d119922 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118488, d119922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d118488, d119922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d118489 q = 0) : d119923 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118489, d119923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118489, d119923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro9186 (p : Pattern) (selected : d118494 p = 0) : d119935 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118485 q = 0) : d119919 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118485, d119919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118485, d119919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9148 q selected
  have h2 (q : Pattern) (selected : d118304 q = 0) : d119736 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118304, d119736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9148 q selected
    | true =>
      simp only [d118304, d119736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118486 q = 0) : d119920 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118486, d119920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118486, d119920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118305 q = 0) : d119737 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118305, d119737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118305, d119737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118487 q = 0) : d119921 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118487, d119921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118487, d119921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118488 q = 0) : d119922 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118488, d119922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118488, d119922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118490 q = 0) : d119931 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118490, d119931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118490, d119931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9150 q selected
  have h8 (q : Pattern) (selected : d118309 q = 0) : d119741 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118309, d119741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9150 q selected
    | true =>
      simp only [d118309, d119741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d118491 q = 0) : d119932 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118491, d119932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118491, d119932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d118310 q = 0) : d119742 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118310, d119742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d118310, d119742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d118492 q = 0) : d119933 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118492, d119933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d118492, d119933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d118493 q = 0) : d119934 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118493, d119934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d118493, d119934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d118494 q = 0) : d119935 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118494, d119935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118494, d119935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro9187 (p : Pattern) (selected : d118502 p = 0) : d119943 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118498 q = 0) : d119939 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118498, d119939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118498, d119939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9152 q selected
  have h2 (q : Pattern) (selected : d118317 q = 0) : d119749 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118317, d119749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9152 q selected
    | true =>
      simp only [d118317, d119749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118499 q = 0) : d119940 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118499, d119940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118499, d119940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118318 q = 0) : d119750 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118318, d119750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118318, d119750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118500 q = 0) : d119941 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118500, d119941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118500, d119941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118501 q = 0) : d119942 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118501, d119942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118501, d119942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118502 q = 0) : d119943 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118502, d119943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118502, d119943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro9188 (p : Pattern) (selected : d118507 p = 0) : d119961 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118490 q = 0) : d119931 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118490, d119931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118490, d119931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9150 q selected
  have h2 (q : Pattern) (selected : d118309 q = 0) : d119741 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118309, d119741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9150 q selected
    | true =>
      simp only [d118309, d119741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118491 q = 0) : d119932 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118491, d119932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118491, d119932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118310 q = 0) : d119742 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118310, d119742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118310, d119742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118492 q = 0) : d119933 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118492, d119933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118492, d119933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118493 q = 0) : d119934 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118493, d119934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118493, d119934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118507 q = 0) : d119961 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118507, d119961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118507, d119961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro9189 (p : Pattern) (selected : d118513 p = 0) : d119976 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118495 q = 0) : d119936 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118495, d119936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9185 q selected
    | true =>
      simp only [d118495, d119936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9186 q selected
  have h2 (q : Pattern) (selected : d118496 q = 0) : d119937 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118496, d119937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118496, d119937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118497 q = 0) : d119938 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118497, d119938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118497, d119938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118503 q = 0) : d119944 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118503, d119944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9186 q selected
    | true =>
      simp only [d118503, d119944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9187 q selected
  have h5 (q : Pattern) (selected : d118504 q = 0) : d119945 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118504, d119945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118504, d119945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118505 q = 0) : d119946 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118505, d119946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118505, d119946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d118506 q = 0) : d119947 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118506, d119947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118506, d119947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118508 q = 0) : d119962 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118508, d119962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9186 q selected
    | true =>
      simp only [d118508, d119962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9188 q selected
  have h9 (q : Pattern) (selected : d118509 q = 0) : d119963 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118509, d119963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118509, d119963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d118510 q = 0) : d119964 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118510, d119964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118510, d119964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d118511 q = 0) : d119965 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118511, d119965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d118511, d119965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d118512 q = 0) : d119975 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d118512, d119975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118512, d119975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d118513 q = 0) : d119976 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d118513, d119976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d118513, d119976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro9190 (p : Pattern) (selected : d118517 p = 0) : d119967 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118508 q = 0) : d119962 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118508, d119962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9186 q selected
    | true =>
      simp only [d118508, d119962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9188 q selected
  have h2 (q : Pattern) (selected : d118509 q = 0) : d119963 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118509, d119963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118509, d119963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118510 q = 0) : d119964 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118510, d119964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118510, d119964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118511 q = 0) : d119965 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118511, d119965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118511, d119965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118516 q = 0) : d119966 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d118516, d119966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118516, d119966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118517 q = 0) : d119967 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d118517, d119967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118517, d119967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9191 (p : Pattern) (selected : d118523 p = 0) : d119982 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118514 q = 0) : d119977 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118514, d119977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9189 q selected
    | true =>
      simp only [d118514, d119977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118515 q = 0) : d119978 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118515, d119978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118515, d119978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118518 q = 0) : d119968 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118518, d119968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9190 q selected
    | true =>
      simp only [d118518, d119968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118519 q = 0) : d119969 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118519, d119969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118519, d119969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118520 q = 0) : d119979 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118520, d119979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118520, d119979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118521 q = 0) : d119980 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118521, d119980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118521, d119980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118522 q = 0) : d119981 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118522, d119981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118522, d119981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d118523 q = 0) : d119982 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118523, d119982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118523, d119982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9192 (p : Pattern) (selected : d118527 p = 0) : d119986 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118518 q = 0) : d119968 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118518, d119968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9190 q selected
    | true =>
      simp only [d118518, d119968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118519 q = 0) : d119969 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118519, d119969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118519, d119969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118524 q = 0) : d119983 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118524, d119983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118524, d119983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118525 q = 0) : d119984 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118525, d119984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118525, d119984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118526 q = 0) : d119985 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118526, d119985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118526, d119985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118527 q = 0) : d119986 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118527, d119986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118527, d119986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9193 (p : Pattern) (selected : d118531 p = 0) : d119976 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118442 q = 0) : d119936 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118442, d119936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9176 q selected
    | true =>
      simp only [d118442, d119936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9177 q selected
  have h2 (q : Pattern) (selected : d118443 q = 0) : d119937 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118443, d119937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118443, d119937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118444 q = 0) : d119938 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118444, d119938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118444, d119938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118450 q = 0) : d119944 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118450, d119944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9177 q selected
    | true =>
      simp only [d118450, d119944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9178 q selected
  have h5 (q : Pattern) (selected : d118451 q = 0) : d119945 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118451, d119945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118451, d119945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118452 q = 0) : d119946 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118452, d119946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118452, d119946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d118453 q = 0) : d119947 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118453, d119947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118453, d119947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118468 q = 0) : d119962 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118468, d119962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9177 q selected
    | true =>
      simp only [d118468, d119962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9182 q selected
  have h9 (q : Pattern) (selected : d118469 q = 0) : d119963 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118469, d119963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118469, d119963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d118470 q = 0) : d119964 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118470, d119964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118470, d119964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d118471 q = 0) : d119965 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118471, d119965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d118471, d119965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d118530 q = 0) : d119975 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d118530, d119975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118530, d119975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d118531 q = 0) : d119976 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d118531, d119976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d118531, d119976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro9194 (p : Pattern) (selected : d118537 p = 0) : d119992 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118532 q = 0) : d119977 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118532, d119977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9193 q selected
    | true =>
      simp only [d118532, d119977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118533 q = 0) : d119978 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118533, d119978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118533, d119978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118534 q = 0) : d119989 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118534, d119989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118534, d119989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118535 q = 0) : d119990 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118535, d119990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118535, d119990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118536 q = 0) : d119991 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118536, d119991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118536, d119991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118537 q = 0) : d119992 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118537, d119992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118537, d119992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9195 (p : Pattern) (selected : d118543 p = 0) : d119998 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118480 q = 0) : d119974 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118480, d119974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9181 q selected
    | true =>
      simp only [d118480, d119974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9184 q selected
  have h2 (q : Pattern) (selected : d118528 q = 0) : d119987 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118528, d119987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9191 q selected
    | true =>
      simp only [d118528, d119987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9192 q selected
  have h3 (q : Pattern) (selected : d118529 q = 0) : d119988 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118529, d119988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118529, d119988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118538 q = 0) : d119993 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118538, d119993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9194 q selected
    | true =>
      simp only [d118538, d119993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118539 q = 0) : d119994 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118539, d119994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118539, d119994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118540 q = 0) : d119995 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118540, d119995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118540, d119995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d118541 q = 0) : d119996 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118541, d119996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118541, d119996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118542 q = 0) : d119997 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118542, d119997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118542, d119997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d118543 q = 0) : d119998 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118543, d119998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118543, d119998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro9196 (p : Pattern) (selected : d118548 p = 0) : d119986 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118474 q = 0) : d119968 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118474, d119968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9183 q selected
    | true =>
      simp only [d118474, d119968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118475 q = 0) : d119969 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118475, d119969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118475, d119969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118545 q = 0) : d119983 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118545, d119983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118545, d119983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118546 q = 0) : d119984 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118546, d119984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118546, d119984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118547 q = 0) : d119985 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118547, d119985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118547, d119985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118548 q = 0) : d119986 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118548, d119986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118548, d119986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9197 (p : Pattern) (selected : d118554 p = 0) : d120005 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118549 q = 0) : d120000 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118549, d120000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9196 q selected
    | true =>
      simp only [d118549, d120000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118550 q = 0) : d120001 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118550, d120001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118550, d120001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118551 q = 0) : d120002 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118551, d120002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118551, d120002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118552 q = 0) : d120003 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118552, d120003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118552, d120003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118553 q = 0) : d120004 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118553, d120004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118553, d120004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118554 q = 0) : d120005 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118554, d120005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118554, d120005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9198 (p : Pattern) (selected : d118560 p = 0) : d120011 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118240 q = 0) : d119785 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118240, d119785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118240, d119785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9133 q selected
  have h2 (q : Pattern) (selected : d118241 q = 0) : d119786 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118241, d119786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118241, d119786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118250 q = 0) : d119795 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118250, d119795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9133 q selected
    | true =>
      simp only [d118250, d119795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9136 q selected
  have h4 (q : Pattern) (selected : d118251 q = 0) : d119796 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118251, d119796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118251, d119796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118252 q = 0) : d119797 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d118252, d119797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118252, d119797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118384 q = 0) : d119878 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118384, d119878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9160 q selected
    | true =>
      simp only [d118384, d119878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9170 q selected
  have h7 (q : Pattern) (selected : d118402 q = 0) : d119896 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118402, d119896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9171 q selected
    | true =>
      simp only [d118402, d119896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9172 q selected
  have h8 (q : Pattern) (selected : d118403 q = 0) : d119897 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118403, d119897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118403, d119897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d118404 q = 0) : d119898 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d118404, d119898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d118404, d119898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d118405 q = 0) : d119899 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d118405, d119899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118405, d119899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d118409 q = 0) : d119903 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118409, d119903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118409, d119903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9173 q selected
  have h12 (q : Pattern) (selected : d118411 q = 0) : d119905 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118411, d119905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118411, d119905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9174 q selected
  have h13 (q : Pattern) (selected : d118412 q = 0) : d119906 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118412, d119906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d118412, d119906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d118413 q = 0) : d119907 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d118413, d119907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d118413, d119907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d118414 q = 0) : d119908 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d118414, d119908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d118414, d119908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d118415 q = 0) : d119909 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d118415, d119909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d118415, d119909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d118544 q = 0) : d119999 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118544, d119999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118544, d119999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9195 q selected
  have h18 (q : Pattern) (selected : d118555 q = 0) : d120006 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118555, d120006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118555, d120006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9197 q selected
  have h19 (q : Pattern) (selected : d118556 q = 0) : d120007 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118556, d120007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d118556, d120007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d118557 q = 0) : d120008 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d118557, d120008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d118557, d120008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d118558 q = 0) : d120009 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d118558, d120009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d118558, d120009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d118559 q = 0) : d120010 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d118559, d120010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d118559, d120010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d118560 q = 0) : d120011 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d118560, d120011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d118560, d120011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro9199 (p : Pattern) (selected : d118566 p = 0) : d120017 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118561 q = 0) : d120012 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d118561, d120012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118561, d120012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9198 q selected
  have h2 (q : Pattern) (selected : d118562 q = 0) : d120013 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d118562, d120013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118562, d120013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118563 q = 0) : d120014 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d118563, d120014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118563, d120014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118564 q = 0) : d120015 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d118564, d120015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118564, d120015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118565 q = 0) : d120016 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d118565, d120016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118565, d120016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118566 q = 0) : d120017 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d118566, d120017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118566, d120017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9200 (p : Pattern) (selected : d118572 p = 0) : d120023 p = 1 := by
  have h0 (q : Pattern) (selected : d117157 q = 0) : d118942 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d117157, d118942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8871 q selected
    | true =>
      simp only [d117157, d118942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8905 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d117450 q = 0) : d119171 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d117450, d119171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117450, d119171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8966 q selected
  have h3 (q : Pattern) (selected : d117451 q = 0) : d119172 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d117451, d119172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117451, d119172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117790 q = 0) : d119429 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d117790, d119429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117790, d119429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9038 q selected
  have h5 (q : Pattern) (selected : d117791 q = 0) : d119430 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d117791, d119430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117791, d119430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117792 q = 0) : d119431 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d117792, d119431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117792, d119431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d118183 q = 0) : d119728 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d118183, d119728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118183, d119728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9120 q selected
  have h8 (q : Pattern) (selected : d118184 q = 0) : d119729 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d118184, d119729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118184, d119729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d118185 q = 0) : d119730 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d118185, d119730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118185, d119730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d118186 q = 0) : d119731 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d118186, d119731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118186, d119731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d118567 q = 0) : d120018 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d118567, d120018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118567, d120018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9199 q selected
  have h12 (q : Pattern) (selected : d118568 q = 0) : d120019 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d118568, d120019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118568, d120019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d118569 q = 0) : d120020 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d118569, d120020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118569, d120020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d118570 q = 0) : d120021 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d118570, d120021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118570, d120021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d118571 q = 0) : d120022 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d118571, d120022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d118571, d120022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d118572 q = 0) : d120023 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d118572, d120023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d118572, d120023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro9201 (p : Pattern) (selected : d118578 p = 0) : d120029 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118573 q = 0) : d120024 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d118573, d120024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9200 q selected
    | true =>
      simp only [d118573, d120024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118574 q = 0) : d120025 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d118574, d120025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118574, d120025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118575 q = 0) : d120026 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d118575, d120026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118575, d120026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118576 q = 0) : d120027 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d118576, d120027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118576, d120027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118577 q = 0) : d120028 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d118577, d120028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118577, d120028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118578 q = 0) : d120029 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d118578, d120029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118578, d120029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9202 (p : Pattern) (selected : d118584 p = 0) : d120035 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118579 q = 0) : d120030 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d118579, d120030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9201 q selected
    | true =>
      simp only [d118579, d120030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118580 q = 0) : d120031 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d118580, d120031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118580, d120031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118581 q = 0) : d120032 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d118581, d120032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118581, d120032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118582 q = 0) : d120033 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d118582, d120033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118582, d120033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118583 q = 0) : d120034 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d118583, d120034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118583, d120034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118584 q = 0) : d120035 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d118584, d120035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118584, d120035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9203 (p : Pattern) (selected : d118590 p = 0) : d120041 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118585 q = 0) : d120036 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d118585, d120036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9202 q selected
    | true =>
      simp only [d118585, d120036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118586 q = 0) : d120037 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d118586, d120037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118586, d120037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118587 q = 0) : d120038 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d118587, d120038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118587, d120038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118588 q = 0) : d120039 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d118588, d120039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118588, d120039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118589 q = 0) : d120040 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d118589, d120040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118589, d120040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118590 q = 0) : d120041 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d118590, d120041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118590, d120041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9204 (p : Pattern) (selected : d118596 p = 0) : d120047 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118591 q = 0) : d120042 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d118591, d120042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9203 q selected
    | true =>
      simp only [d118591, d120042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118592 q = 0) : d120043 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d118592, d120043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118592, d120043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118593 q = 0) : d120044 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d118593, d120044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118593, d120044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118594 q = 0) : d120045 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d118594, d120045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118594, d120045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118595 q = 0) : d120046 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d118595, d120046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118595, d120046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118596 q = 0) : d120047 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d118596, d120047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118596, d120047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9205 (p : Pattern) (selected : d118602 p = 0) : d120053 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118597 q = 0) : d120048 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d118597, d120048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9204 q selected
    | true =>
      simp only [d118597, d120048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118598 q = 0) : d120049 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d118598, d120049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118598, d120049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118599 q = 0) : d120050 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d118599, d120050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118599, d120050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118600 q = 0) : d120051 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d118600, d120051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118600, d120051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118601 q = 0) : d120052 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d118601, d120052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118601, d120052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118602 q = 0) : d120053 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d118602, d120053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118602, d120053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9206 (p : Pattern) (selected : d118608 p = 0) : d120059 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118603 q = 0) : d120054 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d118603, d120054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9205 q selected
    | true =>
      simp only [d118603, d120054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118604 q = 0) : d120055 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d118604, d120055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118604, d120055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118605 q = 0) : d120056 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d118605, d120056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118605, d120056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118606 q = 0) : d120057 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d118606, d120057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118606, d120057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118607 q = 0) : d120058 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d118607, d120058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118607, d120058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118608 q = 0) : d120059 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d118608, d120059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118608, d120059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9207 (p : Pattern) (selected : d118614 p = 0) : d120065 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d118609 q = 0) : d120060 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d118609, d120060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9206 q selected
    | true =>
      simp only [d118609, d120060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118610 q = 0) : d120061 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d118610, d120061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118610, d120061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118611 q = 0) : d120062 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d118611, d120062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118611, d120062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118612 q = 0) : d120063 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d118612, d120063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118612, d120063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118613 q = 0) : d120064 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d118613, d120064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118613, d120064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118614 q = 0) : d120065 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d118614, d120065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118614, d120065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9208 (p : Pattern) (selected : d168 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
    | true =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d165 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d166 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d167 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d168 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro9209 (p : Pattern) (selected : d116877 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d116873 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9208 q selected
    | true =>
      simp only [d116873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116874 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d116875 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d116875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116876 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d116876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116877 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d116877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d116877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro9210 (p : Pattern) (selected : d116883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d116878 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d116878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9209 q selected
    | true =>
      simp only [d116878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116879 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d116879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116880 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d116880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116881 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d116881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116882 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d116882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d116882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d116883 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d116883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9211 (p : Pattern) (selected : d116889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d116884 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9210 q selected
    | true =>
      simp only [d116884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116885 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116886 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d116886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116887 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d116887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116888 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d116888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d116888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d116889 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d116889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9212 (p : Pattern) (selected : d116895 p = 1) : d121569 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d116848 q = 1) : d116848 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d116854 q = 1) : d116854 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d116872 q = 1) : d116872 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d116890 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9211 q selected
    | true =>
      simp only [d116890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116891 q = 1) : d121565 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d116891, d121565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116891, d121565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116772 q = 1) : d116772 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d116892 q = 1) : d121566 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d116892, d121566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116892, d121566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d116893 q = 1) : d121567 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d116893, d121567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116893, d121567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d116894 q = 1) : d121568 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d116894, d121568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116894, d121568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d116895 q = 1) : d121569 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d116895, d121569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116895, d121569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro9213 (p : Pattern) (selected : d116907 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d116884 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9210 q selected
    | true =>
      simp only [d116884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116885 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116886 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d116886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116887 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d116887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116888 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d116888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d116888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d116907 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d116907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9214 (p : Pattern) (selected : d116913 p = 1) : d121574 p = 1 := by
  have h0 (q : Pattern) (selected : d116848 q = 1) : d116848 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d116854 q = 1) : d116854 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d116872 q = 1) : d116872 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d116890 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9211 q selected
    | true =>
      simp only [d116890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d116891 q = 1) : d121565 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d116891, d121565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116891, d121565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116772 q = 1) : d116772 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d116892 q = 1) : d121566 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d116892, d121566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116892, d121566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d116893 q = 1) : d121567 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d116893, d121567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116893, d121567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d116894 q = 1) : d121568 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d116894, d121568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116894, d121568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d116900 q = 1) : d116900 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d116904 q = 1) : d116904 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d116906 q = 1) : d116906 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d116908 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9213 q selected
    | true =>
      simp only [d116908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d116909 q = 1) : d121570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d116909, d121570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d116909, d121570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d116779 q = 1) : d116779 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d116910 q = 1) : d121571 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d116910, d121571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d116910, d121571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d116911 q = 1) : d121572 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d116911, d121572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d116911, d121572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d116912 q = 1) : d121573 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d116912, d121573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d116912, d121573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d116913 q = 1) : d121574 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d116913, d121574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d116913, d121574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro9215 (p : Pattern) (selected : d116922 p = 1) : d121581 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d116906 q = 1) : d116906 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d116908 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9213 q selected
    | true =>
      simp only [d116908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d116909 q = 1) : d121570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d116909, d121570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116909, d121570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116779 q = 1) : d116779 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d116910 q = 1) : d121571 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d116910, d121571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116910, d121571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116920 q = 1) : d121579 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d116920, d121579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116920, d121579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d116921 q = 1) : d121580 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d116921, d121580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116921, d121580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d116922 q = 1) : d121581 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d116922, d121581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116922, d121581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9216 (p : Pattern) (selected : d116950 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d116946 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9208 q selected
  have h2 (q : Pattern) (selected : d116873 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9208 q selected
    | true =>
      simp only [d116873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d116947 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116874 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116948 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d116948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116949 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d116949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d116950 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d116950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d116950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro9217 (p : Pattern) (selected : d116956 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d116951 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d116951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9216 q selected
    | true =>
      simp only [d116951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116952 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d116952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116953 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d116953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116954 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d116954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116955 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d116955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d116955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d116956 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d116956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9218 (p : Pattern) (selected : d116962 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d116957 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9217 q selected
    | true =>
      simp only [d116957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d116958 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116959 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d116959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d116959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116960 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d116960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116961 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d116961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d116961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d116962 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d116962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9219 (p : Pattern) (selected : d116968 p = 1) : d121591 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d116945 q = 1) : d116945 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d116963 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d116963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9218 q selected
    | true =>
      simp only [d116963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d116964 q = 1) : d121587 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d116964, d121587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116964, d121587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116812 q = 1) : d116812 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d116965 q = 1) : d121588 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d116965, d121588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116965, d121588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116966 q = 1) : d121589 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d116966, d121589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116966, d121589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d116967 q = 1) : d121590 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d116967, d121590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116967, d121590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d116968 q = 1) : d121591 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d116968, d121591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116968, d121591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9220 (p : Pattern) (selected : d116974 p = 1) : d121597 p = 1 := by
  have h0 (q : Pattern) (selected : d116842 q = 1) : d116842 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d116914 q = 1) : d121575 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d116914, d121575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9212 q selected
    | true =>
      simp only [d116914, d121575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9214 q selected
  have h2 (q : Pattern) (selected : d116916 q = 1) : d116916 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d116917 q = 1) : d121576 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d116917, d121576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116917, d121576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d116918 q = 1) : d121577 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d116918, d121577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d116918, d121577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116919 q = 1) : d121578 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d116919, d121578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116919, d121578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d116923 q = 1) : d121582 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d116923, d121582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d116923, d121582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9215 q selected
  have h8 (q : Pattern) (selected : d116924 q = 1) : d121583 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d116924, d121583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d116924, d121583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d116925 q = 1) : d121584 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d116925, d121584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d116925, d121584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d116926 q = 1) : d121585 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d116926, d121585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d116926, d121585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d116927 q = 1) : d121586 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d116927, d121586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d116927, d121586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d116969 q = 1) : d121592 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d116969, d121592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d116969, d121592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9219 q selected
  have h13 (q : Pattern) (selected : d116970 q = 1) : d121593 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d116970, d121593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d116970, d121593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d116971 q = 1) : d121594 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d116971, d121594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d116971, d121594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d116972 q = 1) : d121595 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d116972, d121595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d116972, d121595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d116973 q = 1) : d121596 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d116973, d121596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d116973, d121596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d116974 q = 1) : d121597 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d116974, d121597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d116974, d121597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro9221 (p : Pattern) (selected : d116980 p = 1) : d121603 p = 1 := by
  have h0 (q : Pattern) (selected : d116827 q = 1) : d116827 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d116975 q = 1) : d121598 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d116975, d121598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116975, d121598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9220 q selected
  have h3 (q : Pattern) (selected : d116976 q = 1) : d121599 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d116976, d121599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116976, d121599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116977 q = 1) : d121600 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d116977, d121600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116977, d121600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d116978 q = 1) : d121601 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d116978, d121601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116978, d121601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116979 q = 1) : d121602 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d116979, d121602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d116979, d121602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d116980 q = 1) : d121603 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d116980, d121603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116980, d121603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro9222 (p : Pattern) (selected : d348 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d344 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14 q selected
    | true =>
      simp only [d344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d345 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
    | true =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d165 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d346 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d347 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d348 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9223 (p : Pattern) (selected : d117030 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117026 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9222 q selected
    | true =>
      simp only [d117026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117027 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117028 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117029 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116873 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9208 q selected
    | true =>
      simp only [d116873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d116874 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d116874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d116875 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d116875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d116876 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d116876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d116876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117030 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro9224 (p : Pattern) (selected : d117036 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117031 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9223 q selected
    | true =>
      simp only [d117031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9209 q selected
  have h2 (q : Pattern) (selected : d117032 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117033 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116878 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d116878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9209 q selected
    | true =>
      simp only [d116878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116879 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d116879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116880 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d116880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117034 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d116881 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d116881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d116881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117035 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117036 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro9225 (p : Pattern) (selected : d117042 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117037 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9224 q selected
    | true =>
      simp only [d117037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117038 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116884 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9210 q selected
    | true =>
      simp only [d116884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116885 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117039 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117040 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117041 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117042 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9226 (p : Pattern) (selected : d117054 p = 1) : d121608 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117001 q = 1) : d117001 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d117007 q = 1) : d117007 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d117025 q = 1) : d117025 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d117043 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9225 q selected
    | true =>
      simp only [d117043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9211 q selected
  have h5 (q : Pattern) (selected : d117044 q = 1) : d121604 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117044, d121604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117044, d121604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117050 q = 1) : d117050 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d117051 q = 1) : d121605 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117051, d121605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117051, d121605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117052 q = 1) : d121606 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117052, d121606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117052, d121606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d117053 q = 1) : d121607 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117053, d121607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117053, d121607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117054 q = 1) : d121608 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117054, d121608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117054, d121608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro9227 (p : Pattern) (selected : d117066 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117037 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9224 q selected
    | true =>
      simp only [d117037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117038 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116884 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9210 q selected
    | true =>
      simp only [d116884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116885 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117039 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117040 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117041 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117066 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9228 (p : Pattern) (selected : d117075 p = 1) : d121613 p = 1 := by
  have h0 (q : Pattern) (selected : d117001 q = 1) : d117001 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117007 q = 1) : d117007 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d117025 q = 1) : d117025 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d117043 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9225 q selected
    | true =>
      simp only [d117043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9211 q selected
  have h4 (q : Pattern) (selected : d117044 q = 1) : d121604 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117044, d121604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117044, d121604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117050 q = 1) : d117050 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d117051 q = 1) : d121605 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117051, d121605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117051, d121605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117052 q = 1) : d121606 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117052, d121606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117052, d121606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117053 q = 1) : d121607 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117053, d121607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117053, d121607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d117059 q = 1) : d117059 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d117063 q = 1) : d117063 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d117065 q = 1) : d117065 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d117067 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9227 q selected
    | true =>
      simp only [d117067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9213 q selected
  have h13 (q : Pattern) (selected : d117068 q = 1) : d121609 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117068, d121609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d117068, d121609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d117071 q = 1) : d117071 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d117072 q = 1) : d121610 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117072, d121610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d117072, d121610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d117073 q = 1) : d121611 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117073, d121611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d117073, d121611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d117074 q = 1) : d121612 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117074, d121612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117074, d121612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d117075 q = 1) : d121613 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117075, d121613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117075, d121613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro9229 (p : Pattern) (selected : d117084 p = 1) : d121620 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117065 q = 1) : d117065 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d117067 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9227 q selected
    | true =>
      simp only [d117067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9213 q selected
  have h3 (q : Pattern) (selected : d117068 q = 1) : d121609 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117068, d121609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117068, d121609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117071 q = 1) : d117071 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d117072 q = 1) : d121610 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117072, d121610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117072, d121610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117082 q = 1) : d121618 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117082, d121618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117082, d121618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117083 q = 1) : d121619 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117083, d121619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117083, d121619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117084 q = 1) : d121620 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117084, d121620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117084, d121620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9230 (p : Pattern) (selected : d117114 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117110 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9222 q selected
  have h2 (q : Pattern) (selected : d117026 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9222 q selected
    | true =>
      simp only [d117026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117111 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117027 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117112 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117113 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d116946 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9208 q selected
  have h8 (q : Pattern) (selected : d116873 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d116873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9208 q selected
    | true =>
      simp only [d116873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d116947 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d116947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d116874 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d116874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d116874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d116948 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d116948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d116948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d116949 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d116949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d116949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d117114 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro9231 (p : Pattern) (selected : d117120 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117115 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9230 q selected
    | true =>
      simp only [d117115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9216 q selected
  have h2 (q : Pattern) (selected : d117116 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117117 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d116951 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d116951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9216 q selected
    | true =>
      simp only [d116951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d116952 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d116952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d116953 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d116953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117118 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d116954 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d116954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d116954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117119 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117120 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro9232 (p : Pattern) (selected : d117126 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117121 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9231 q selected
    | true =>
      simp only [d117121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117122 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d116957 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d116957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9217 q selected
    | true =>
      simp only [d116957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d116958 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d116958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d116958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117123 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117124 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117125 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117126 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9233 (p : Pattern) (selected : d117138 p = 1) : d121630 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117109 q = 1) : d117109 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d117127 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9232 q selected
    | true =>
      simp only [d117127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9218 q selected
  have h3 (q : Pattern) (selected : d117128 q = 1) : d121626 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117128, d121626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117128, d121626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117134 q = 1) : d117134 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d117135 q = 1) : d121627 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117135, d121627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117135, d121627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117136 q = 1) : d121628 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117136, d121628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117136, d121628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117137 q = 1) : d121629 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117137, d121629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117137, d121629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117138 q = 1) : d121630 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117138, d121630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117138, d121630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9234 (p : Pattern) (selected : d117150 p = 1) : d121636 p = 1 := by
  have h0 (q : Pattern) (selected : d116995 q = 1) : d116995 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117076 q = 1) : d121614 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d117076, d121614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9226 q selected
    | true =>
      simp only [d117076, d121614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9228 q selected
  have h2 (q : Pattern) (selected : d117078 q = 1) : d117078 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d117079 q = 1) : d121615 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d117079, d121615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117079, d121615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d117080 q = 1) : d121616 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d117080, d121616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117080, d121616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117081 q = 1) : d121617 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d117081, d121617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117081, d121617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117085 q = 1) : d121621 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d117085, d121621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117085, d121621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9229 q selected
  have h8 (q : Pattern) (selected : d117087 q = 1) : d117087 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d117088 q = 1) : d121622 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d117088, d121622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117088, d121622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117089 q = 1) : d121623 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d117089, d121623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117089, d121623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d117090 q = 1) : d121624 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d117090, d121624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d117090, d121624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d117091 q = 1) : d121625 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d117091, d121625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117091, d121625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d117139 q = 1) : d121631 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d117139, d121631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117139, d121631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9233 q selected
  have h14 (q : Pattern) (selected : d117145 q = 1) : d117145 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d117146 q = 1) : d121632 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d117146, d121632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d117146, d121632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d117147 q = 1) : d121633 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d117147, d121633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d117147, d121633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d117148 q = 1) : d121634 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d117148, d121634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d117148, d121634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d117149 q = 1) : d121635 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d117149, d121635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d117149, d121635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d117150 q = 1) : d121636 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d117150, d121636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d117150, d121636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro9235 (p : Pattern) (selected : d117156 p = 1) : d121642 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117151 q = 1) : d121637 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d117151, d121637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117151, d121637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9234 q selected
  have h2 (q : Pattern) (selected : d117152 q = 1) : d121638 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d117152, d121638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117152, d121638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117153 q = 1) : d121639 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d117153, d121639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117153, d121639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117154 q = 1) : d121640 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d117154, d121640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117154, d121640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117155 q = 1) : d121641 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d117155, d121641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117155, d121641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117156 q = 1) : d121642 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d117156, d121642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117156, d121642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9236 (p : Pattern) (selected : d572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d568 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro29 q selected
    | true =>
      simp only [d568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d569 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d344 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14 q selected
    | true =>
      simp only [d344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d345 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d570 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
    | true =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d165 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d346 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d571 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d572 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro9237 (p : Pattern) (selected : d117249 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117245 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9236 q selected
    | true =>
      simp only [d117245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117246 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117247 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117248 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117026 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9222 q selected
    | true =>
      simp only [d117026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117027 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117028 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117029 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117249 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro9238 (p : Pattern) (selected : d117250 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117026 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9222 q selected
    | true =>
      simp only [d117026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117027 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117028 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117029 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117250 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro9239 (p : Pattern) (selected : d117260 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117251 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9237 q selected
    | true =>
      simp only [d117251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9238 q selected
  have h2 (q : Pattern) (selected : d117252 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117253 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117254 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9238 q selected
    | true =>
      simp only [d117254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117255 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117256 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117257 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117258 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117259 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117260 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro9240 (p : Pattern) (selected : d117264 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117254 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9238 q selected
    | true =>
      simp only [d117254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117255 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117256 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117258 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117263 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117264 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9241 (p : Pattern) (selected : d117270 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117261 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9239 q selected
    | true =>
      simp only [d117261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117262 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117265 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9240 q selected
    | true =>
      simp only [d117265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117266 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117267 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117268 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117269 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117270 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9242 (p : Pattern) (selected : d117274 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117265 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9240 q selected
    | true =>
      simp only [d117265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117266 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117271 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117272 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117273 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117274 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9243 (p : Pattern) (selected : d117286 p = 1) : d121648 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117209 q = 1) : d117209 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d117218 q = 1) : d117218 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d117244 q = 1) : d117244 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d117275 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9241 q selected
    | true =>
      simp only [d117275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9242 q selected
  have h5 (q : Pattern) (selected : d117276 q = 1) : d121644 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117276, d121644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117276, d121644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117282 q = 1) : d117282 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d117283 q = 1) : d121645 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117283, d121645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117283, d121645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117284 q = 1) : d121646 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117284, d121646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117284, d121646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d117285 q = 1) : d121647 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117285, d121647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117285, d121647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117286 q = 1) : d121648 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117286, d121648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117286, d121648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro9244 (p : Pattern) (selected : d117300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117261 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9239 q selected
    | true =>
      simp only [d117261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117262 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117265 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9240 q selected
    | true =>
      simp only [d117265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117266 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117267 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117268 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117269 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117300 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9245 (p : Pattern) (selected : d117301 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117265 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9240 q selected
    | true =>
      simp only [d117265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117266 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117271 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117272 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117273 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117301 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9246 (p : Pattern) (selected : d117310 p = 1) : d121653 p = 1 := by
  have h0 (q : Pattern) (selected : d117209 q = 1) : d117209 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117218 q = 1) : d117218 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d117244 q = 1) : d117244 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d117275 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9241 q selected
    | true =>
      simp only [d117275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9242 q selected
  have h4 (q : Pattern) (selected : d117276 q = 1) : d121644 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117276, d121644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117276, d121644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117282 q = 1) : d117282 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d117283 q = 1) : d121645 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117283, d121645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117283, d121645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117284 q = 1) : d121646 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117284, d121646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117284, d121646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117285 q = 1) : d121647 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117285, d121647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117285, d121647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d117292 q = 1) : d117292 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d117297 q = 1) : d117297 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d117299 q = 1) : d117299 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d117302 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9244 q selected
    | true =>
      simp only [d117302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9245 q selected
  have h13 (q : Pattern) (selected : d117303 q = 1) : d121649 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117303, d121649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d117303, d121649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d117306 q = 1) : d117306 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d117307 q = 1) : d121650 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117307, d121650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d117307, d121650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d117308 q = 1) : d121651 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117308, d121651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d117308, d121651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d117309 q = 1) : d121652 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117309, d121652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117309, d121652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d117310 q = 1) : d121653 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117310, d121653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117310, d121653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro9247 (p : Pattern) (selected : d117330 p = 1) : d121660 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117299 q = 1) : d117299 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d117302 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9244 q selected
    | true =>
      simp only [d117302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9245 q selected
  have h3 (q : Pattern) (selected : d117303 q = 1) : d121649 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117303, d121649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117303, d121649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117306 q = 1) : d117306 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d117307 q = 1) : d121650 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117307, d121650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117307, d121650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117328 q = 1) : d121658 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117328, d121658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117328, d121658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117329 q = 1) : d121659 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117329, d121659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117329, d121659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117330 q = 1) : d121660 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117330, d121660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117330, d121660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9248 (p : Pattern) (selected : d117389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117385 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9236 q selected
  have h2 (q : Pattern) (selected : d117245 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9236 q selected
    | true =>
      simp only [d117245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117386 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117246 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117387 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117388 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117110 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9222 q selected
  have h8 (q : Pattern) (selected : d117026 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9222 q selected
    | true =>
      simp only [d117026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117111 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117027 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d117112 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d117113 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d117113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d117389 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro9249 (p : Pattern) (selected : d117390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117110 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9222 q selected
  have h2 (q : Pattern) (selected : d117026 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9222 q selected
    | true =>
      simp only [d117026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117111 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117027 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117112 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117113 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117390 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
end NetHack.Soko22Hazard87
