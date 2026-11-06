import NetHack.Soko22Hazard87.EqIntroBlocks0058
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro14750 (p : Pattern) (selected : d164270 p = 0) : d165531 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164195 q = 0) : d165488 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164195, d165488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14734 q selected
    | true =>
      simp only [d164195, d165488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14735 q selected
  have h2 (q : Pattern) (selected : d164196 q = 0) : d165489 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164196, d165489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164196, d165489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164197 q = 0) : d165490 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164197, d165490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164197, d165490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164198 q = 0) : d165491 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164198, d165491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164198, d165491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164205 q = 0) : d165498 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164205, d165498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14736 q selected
    | true =>
      simp only [d164205, d165498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14737 q selected
  have h6 (q : Pattern) (selected : d164206 q = 0) : d165499 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164206, d165499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164206, d165499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164207 q = 0) : d165500 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164207, d165500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164207, d165500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164227 q = 0) : d165520 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164227, d165520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14741 q selected
    | true =>
      simp only [d164227, d165520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14728 q selected
  have h9 (q : Pattern) (selected : d164259 q = 0) : d165465 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164259, d165465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14747 q selected
    | true =>
      simp only [d164259, d165465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14748 q selected
  have h10 (q : Pattern) (selected : d164260 q = 0) : d165521 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164260, d165521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d164260, d165521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164265 q = 0) : d165526 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164265, d165526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14749 q selected
    | true =>
      simp only [d164265, d165526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d164266 q = 0) : d165527 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164266, d165527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d164266, d165527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d164267 q = 0) : d165528 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164267, d165528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164267, d165528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d164268 q = 0) : d165529 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164268, d165529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164268, d165529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d164269 q = 0) : d165530 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164269, d165530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164269, d165530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d164270 q = 0) : d165531 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164270, d165531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164270, d165531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro14751 (p : Pattern) (selected : d164271 p = 0) : d165532 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164158 q = 0) : d165451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164158, d165451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14726 q selected
    | true =>
      simp only [d164158, d165451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164159 q = 0) : d165452 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164159, d165452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164159, d165452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164162 q = 0) : d165455 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164162, d165455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14727 q selected
    | true =>
      simp only [d164162, d165455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164163 q = 0) : d165456 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164163, d165456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164163, d165456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164164 q = 0) : d165457 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164164, d165457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164164, d165457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164165 q = 0) : d165458 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164165, d165458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164165, d165458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164191 q = 0) : d165484 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164191, d165484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164191, d165484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164271 q = 0) : d165532 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164271, d165532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164271, d165532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14752 (p : Pattern) (selected : d164272 p = 0) : d165533 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164162 q = 0) : d165455 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164162, d165455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14727 q selected
    | true =>
      simp only [d164162, d165455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164163 q = 0) : d165456 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164163, d165456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164163, d165456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164168 q = 0) : d165461 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164168, d165461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164168, d165461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164169 q = 0) : d165462 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164169, d165462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164169, d165462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164193 q = 0) : d165486 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164193, d165486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164193, d165486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164272 q = 0) : d165533 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164272, d165533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164272, d165533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14753 (p : Pattern) (selected : d164277 p = 0) : d165538 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164158 q = 0) : d165451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164158, d165451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14726 q selected
    | true =>
      simp only [d164158, d165451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164159 q = 0) : d165452 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164159, d165452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164159, d165452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164162 q = 0) : d165455 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164162, d165455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14727 q selected
    | true =>
      simp only [d164162, d165455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164163 q = 0) : d165456 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164163, d165456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164163, d165456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164164 q = 0) : d165457 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164164, d165457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164164, d165457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164199 q = 0) : d165492 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164199, d165492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164199, d165492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164200 q = 0) : d165493 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164200, d165493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164200, d165493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164277 q = 0) : d165538 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164277, d165538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164277, d165538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14754 (p : Pattern) (selected : d164278 p = 0) : d165539 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164162 q = 0) : d165455 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164162, d165455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14727 q selected
    | true =>
      simp only [d164162, d165455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164163 q = 0) : d165456 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164163, d165456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164163, d165456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164168 q = 0) : d165461 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164168, d165461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164168, d165461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164202 q = 0) : d165495 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164202, d165495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164202, d165495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164203 q = 0) : d165496 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164203, d165496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164203, d165496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164278 q = 0) : d165539 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164278, d165539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164278, d165539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14755 (p : Pattern) (selected : d164282 p = 0) : d165543 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164221 q = 0) : d165514 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164221, d165514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14740 q selected
    | true =>
      simp only [d164221, d165514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164222 q = 0) : d165515 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164222, d165515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164222, d165515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164158 q = 0) : d165451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164158, d165451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14726 q selected
    | true =>
      simp only [d164158, d165451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164159 q = 0) : d165452 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164159, d165452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164159, d165452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164223 q = 0) : d165516 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164223, d165516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164223, d165516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164224 q = 0) : d165517 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164224, d165517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164224, d165517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164225 q = 0) : d165518 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164225, d165518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164225, d165518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164282 q = 0) : d165543 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164282, d165543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164282, d165543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14756 (p : Pattern) (selected : d164284 p = 0) : d165473 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164245 q = 0) : d165451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164245, d165451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14745 q selected
    | true =>
      simp only [d164245, d165451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164246 q = 0) : d165452 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164246, d165452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164246, d165452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164249 q = 0) : d165455 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164249, d165455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14746 q selected
    | true =>
      simp only [d164249, d165455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164250 q = 0) : d165456 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164250, d165456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164250, d165456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164251 q = 0) : d165457 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164251, d165457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164251, d165457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164252 q = 0) : d165458 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164252, d165458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164252, d165458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164253 q = 0) : d165459 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164253, d165459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164253, d165459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164284 q = 0) : d165473 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164284, d165473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164284, d165473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14757 (p : Pattern) (selected : d164285 p = 0) : d165474 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164249 q = 0) : d165455 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164249, d165455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14746 q selected
    | true =>
      simp only [d164249, d165455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164250 q = 0) : d165456 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164250, d165456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164250, d165456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164255 q = 0) : d165461 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164255, d165461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164255, d165461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164256 q = 0) : d165462 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164256, d165462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164256, d165462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164257 q = 0) : d165463 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164257, d165463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164257, d165463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164285 q = 0) : d165474 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164285, d165474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164285, d165474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14758 (p : Pattern) (selected : d164288 p = 0) : d165546 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164158 q = 0) : d165451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164158, d165451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14726 q selected
    | true =>
      simp only [d164158, d165451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164159 q = 0) : d165452 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164159, d165452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164159, d165452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164261 q = 0) : d165522 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164261, d165522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164261, d165522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164262 q = 0) : d165523 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164262, d165523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164262, d165523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164263 q = 0) : d165524 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164263, d165524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164263, d165524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164288 q = 0) : d165546 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164288, d165546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164288, d165546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14759 (p : Pattern) (selected : d164294 p = 0) : d165552 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164195 q = 0) : d165488 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164195, d165488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14734 q selected
    | true =>
      simp only [d164195, d165488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14735 q selected
  have h2 (q : Pattern) (selected : d164196 q = 0) : d165489 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164196, d165489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164196, d165489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164197 q = 0) : d165490 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164197, d165490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164197, d165490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164198 q = 0) : d165491 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164198, d165491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164198, d165491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164205 q = 0) : d165498 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164205, d165498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14736 q selected
    | true =>
      simp only [d164205, d165498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14737 q selected
  have h6 (q : Pattern) (selected : d164206 q = 0) : d165499 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164206, d165499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164206, d165499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164207 q = 0) : d165500 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164207, d165500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164207, d165500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164227 q = 0) : d165520 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164227, d165520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14741 q selected
    | true =>
      simp only [d164227, d165520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14728 q selected
  have h9 (q : Pattern) (selected : d164259 q = 0) : d165465 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164259, d165465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14747 q selected
    | true =>
      simp only [d164259, d165465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14748 q selected
  have h10 (q : Pattern) (selected : d164260 q = 0) : d165521 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164260, d165521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d164260, d165521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164265 q = 0) : d165526 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164265, d165526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14749 q selected
    | true =>
      simp only [d164265, d165526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d164266 q = 0) : d165527 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164266, d165527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d164266, d165527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d164267 q = 0) : d165528 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164267, d165528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164267, d165528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d164268 q = 0) : d165529 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164268, d165529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164268, d165529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d164269 q = 0) : d165530 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164269, d165530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164269, d165530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d164273 q = 0) : d165534 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164273, d165534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14751 q selected
    | true =>
      simp only [d164273, d165534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14752 q selected
  have h17 (q : Pattern) (selected : d164274 q = 0) : d165535 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164274, d165535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164274, d165535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d164275 q = 0) : d165536 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164275, d165536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d164275, d165536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d164276 q = 0) : d165537 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164276, d165537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164276, d165537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d164279 q = 0) : d165540 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164279, d165540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14753 q selected
    | true =>
      simp only [d164279, d165540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14754 q selected
  have h21 (q : Pattern) (selected : d164280 q = 0) : d165541 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164280, d165541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164280, d165541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d164281 q = 0) : d165542 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164281, d165542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d164281, d165542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d164283 q = 0) : d165544 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164283, d165544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14755 q selected
    | true =>
      simp only [d164283, d165544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14731 q selected
  have h24 (q : Pattern) (selected : d164286 q = 0) : d165475 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164286, d165475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14756 q selected
    | true =>
      simp only [d164286, d165475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14757 q selected
  have h25 (q : Pattern) (selected : d164287 q = 0) : d165545 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164287, d165545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d164287, d165545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d164289 q = 0) : d165547 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164289, d165547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14758 q selected
    | true =>
      simp only [d164289, d165547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d164290 q = 0) : d165548 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164290, d165548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d164290, d165548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d164291 q = 0) : d165549 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164291, d165549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d164291, d165549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d164292 q = 0) : d165550 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164292, d165550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d164292, d165550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d164293 q = 0) : d165551 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164293, d165551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d164293, d165551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d164294 q = 0) : d165552 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164294, d165552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d164294, d165552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro14760 (p : Pattern) (selected : d164301 p = 0) : d165559 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164172 q = 0) : d165465 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164172, d165465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14728 q selected
    | true =>
      simp only [d164172, d165465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14729 q selected
  have h2 (q : Pattern) (selected : d164173 q = 0) : d165466 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164173, d165466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164173, d165466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164174 q = 0) : d165467 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164174, d165467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164174, d165467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164175 q = 0) : d165468 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164175, d165468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164175, d165468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164176 q = 0) : d165469 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164176, d165469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164176, d165469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164296 q = 0) : d165554 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164296, d165554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14729 q selected
    | true =>
      simp only [d164296, d165554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164297 q = 0) : d165555 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164297, d165555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164297, d165555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164298 q = 0) : d165556 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164298, d165556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164298, d165556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d164299 q = 0) : d165557 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164299, d165557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164299, d165557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164300 q = 0) : d165558 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164300, d165558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164300, d165558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164301 q = 0) : d165559 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164301, d165559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164301, d165559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14761 (p : Pattern) (selected : d164307 p = 0) : d165565 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164296 q = 0) : d165554 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164296, d165554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14729 q selected
    | true =>
      simp only [d164296, d165554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164297 q = 0) : d165555 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164297, d165555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164297, d165555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164298 q = 0) : d165556 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164298, d165556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164298, d165556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164299 q = 0) : d165557 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164299, d165557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164299, d165557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164300 q = 0) : d165558 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164300, d165558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164300, d165558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164302 q = 0) : d165560 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164302, d165560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14732 q selected
    | true =>
      simp only [d164302, d165560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164303 q = 0) : d165561 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164303, d165561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164303, d165561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164304 q = 0) : d165562 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164304, d165562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164304, d165562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d164305 q = 0) : d165563 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164305, d165563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164305, d165563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164306 q = 0) : d165564 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164306, d165564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164306, d165564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164307 q = 0) : d165565 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164307, d165565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164307, d165565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14762 (p : Pattern) (selected : d164314 p = 0) : d165572 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164283 q = 0) : d165544 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164283, d165544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14755 q selected
    | true =>
      simp only [d164283, d165544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14731 q selected
  have h2 (q : Pattern) (selected : d164286 q = 0) : d165475 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164286, d165475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14756 q selected
    | true =>
      simp only [d164286, d165475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14757 q selected
  have h3 (q : Pattern) (selected : d164287 q = 0) : d165545 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164287, d165545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164287, d165545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164289 q = 0) : d165547 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164289, d165547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14758 q selected
    | true =>
      simp only [d164289, d165547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164290 q = 0) : d165548 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164290, d165548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164290, d165548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164291 q = 0) : d165549 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164291, d165549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164291, d165549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164312 q = 0) : d165570 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164312, d165570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164312, d165570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164313 q = 0) : d165571 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164313, d165571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164313, d165571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d164314 q = 0) : d165572 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164314, d165572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164314, d165572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro14763 (p : Pattern) (selected : d164316 p = 0) : d165574 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164302 q = 0) : d165560 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164302, d165560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14732 q selected
    | true =>
      simp only [d164302, d165560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164303 q = 0) : d165561 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164303, d165561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164303, d165561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164304 q = 0) : d165562 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164304, d165562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164304, d165562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164305 q = 0) : d165563 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164305, d165563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164305, d165563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164306 q = 0) : d165564 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164306, d165564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164306, d165564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164316 q = 0) : d165574 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164316, d165574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164316, d165574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14764 (p : Pattern) (selected : d164323 p = 0) : d165581 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164178 q = 0) : d165471 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d164178, d165471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164178, d165471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14730 q selected
  have h2 (q : Pattern) (selected : d164179 q = 0) : d165472 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d164179, d165472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164179, d165472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164188 q = 0) : d165481 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d164188, d165481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14730 q selected
    | true =>
      simp only [d164188, d165481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14733 q selected
  have h4 (q : Pattern) (selected : d164189 q = 0) : d165482 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d164189, d165482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164189, d165482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164190 q = 0) : d165483 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d164190, d165483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164190, d165483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164295 q = 0) : d165553 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d164295, d165553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14750 q selected
    | true =>
      simp only [d164295, d165553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14759 q selected
  have h7 (q : Pattern) (selected : d164308 q = 0) : d165566 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d164308, d165566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14760 q selected
    | true =>
      simp only [d164308, d165566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14761 q selected
  have h8 (q : Pattern) (selected : d164309 q = 0) : d165567 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d164309, d165567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164309, d165567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d164310 q = 0) : d165568 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d164310, d165568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d164310, d165568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d164311 q = 0) : d165569 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d164311, d165569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164311, d165569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164315 q = 0) : d165573 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d164315, d165573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164315, d165573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14762 q selected
  have h12 (q : Pattern) (selected : d164317 q = 0) : d165575 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d164317, d165575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164317, d165575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14763 q selected
  have h13 (q : Pattern) (selected : d164318 q = 0) : d165576 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d164318, d165576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d164318, d165576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d164319 q = 0) : d165577 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d164319, d165577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d164319, d165577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d164320 q = 0) : d165578 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d164320, d165578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d164320, d165578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d164321 q = 0) : d165579 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d164321, d165579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164321, d165579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d164322 q = 0) : d165580 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d164322, d165580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d164322, d165580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d164323 q = 0) : d165581 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d164323, d165581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d164323, d165581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro14765 (p : Pattern) (selected : d164329 p = 0) : d165587 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164324 q = 0) : d165582 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d164324, d165582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164324, d165582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14764 q selected
  have h2 (q : Pattern) (selected : d164325 q = 0) : d165583 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d164325, d165583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164325, d165583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164326 q = 0) : d165584 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d164326, d165584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164326, d165584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164327 q = 0) : d165585 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d164327, d165585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164327, d165585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164328 q = 0) : d165586 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d164328, d165586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164328, d165586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164329 q = 0) : d165587 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d164329, d165587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164329, d165587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14766 (p : Pattern) (selected : d164334 p = 0) : d165592 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1100 q = 0) : d52681 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro386 q selected
    | true =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1101 q = 0) : d52682 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d9789 q = 0) : d101310 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9789, d101310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6674 q selected
    | true =>
      simp only [d9789, d101310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9791 q = 0) : d101312 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9791, d101312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9791, d101312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164332 q = 0) : d165590 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164332, d165590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164332, d165590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9778 q = 0) : d101299 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6672 q selected
    | true =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9780 q = 0) : d101301 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9780, d101301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9780, d101301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9800 q = 0) : d101321 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6675 q selected
    | true =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d9802 q = 0) : d101323 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d164333 q = 0) : d165591 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164333, d165591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164333, d165591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164334 q = 0) : d165592 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164334, d165592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164334, d165592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14767 (p : Pattern) (selected : d164337 p = 0) : d165595 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1110 q = 0) : d52691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro387 q selected
    | true =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1111 q = 0) : d52692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1121 q = 0) : d52702 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro388 q selected
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1122 q = 0) : d52703 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164335 q = 0) : d165593 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164335, d165593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164335, d165593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9800 q = 0) : d101321 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6675 q selected
    | true =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9802 q = 0) : d101323 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164336 q = 0) : d165594 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164336, d165594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164336, d165594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d164337 q = 0) : d165595 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164337, d165595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164337, d165595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro14768 (p : Pattern) (selected : d164343 p = 0) : d165601 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d5018 q = 0) : d69108 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5018, d69108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2799 q selected
    | true =>
      simp only [d5018, d69108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d5019 q = 0) : d69109 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5019, d69109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d5019, d69109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164341 q = 0) : d165599 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164341, d165599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164341, d165599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9844 q = 0) : d101365 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6680 q selected
    | true =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9846 q = 0) : d101367 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164342 q = 0) : d165600 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164342, d165600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164342, d165600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164343 q = 0) : d165601 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164343, d165601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164343, d165601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro14769 (p : Pattern) (selected : d164349 p = 0) : d165607 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1121 q = 0) : d52702 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro388 q selected
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1122 q = 0) : d52703 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164348 q = 0) : d165606 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164348, d165606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164348, d165606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9844 q = 0) : d101365 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6680 q selected
    | true =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9846 q = 0) : d101367 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164342 q = 0) : d165600 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164342, d165600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164342, d165600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164349 q = 0) : d165607 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164349, d165607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164349, d165607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro14770 (p : Pattern) (selected : d164355 p = 0) : d165613 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164338 q = 0) : d165596 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164338, d165596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14766 q selected
    | true =>
      simp only [d164338, d165596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14767 q selected
  have h2 (q : Pattern) (selected : d164339 q = 0) : d165597 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164339, d165597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164339, d165597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164340 q = 0) : d165598 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164340, d165598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164340, d165598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164344 q = 0) : d165602 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164344, d165602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14767 q selected
    | true =>
      simp only [d164344, d165602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14768 q selected
  have h5 (q : Pattern) (selected : d164345 q = 0) : d165603 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164345, d165603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164345, d165603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164346 q = 0) : d165604 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164346, d165604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164346, d165604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164347 q = 0) : d165605 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164347, d165605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164347, d165605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164350 q = 0) : d165608 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164350, d165608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14767 q selected
    | true =>
      simp only [d164350, d165608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14769 q selected
  have h9 (q : Pattern) (selected : d164351 q = 0) : d165609 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164351, d165609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164351, d165609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164352 q = 0) : d165610 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164352, d165610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164352, d165610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164353 q = 0) : d165611 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164353, d165611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164353, d165611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d164354 q = 0) : d165612 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164354, d165612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164354, d165612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d164355 q = 0) : d165613 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164355, d165613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d164355, d165613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro14771 (p : Pattern) (selected : d164359 p = 0) : d165617 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164350 q = 0) : d165608 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164350, d165608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14767 q selected
    | true =>
      simp only [d164350, d165608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14769 q selected
  have h2 (q : Pattern) (selected : d164351 q = 0) : d165609 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164351, d165609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164351, d165609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164352 q = 0) : d165610 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164352, d165610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164352, d165610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164353 q = 0) : d165611 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164353, d165611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164353, d165611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164358 q = 0) : d165616 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164358, d165616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164358, d165616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164359 q = 0) : d165617 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164359, d165617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164359, d165617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14772 (p : Pattern) (selected : d164365 p = 0) : d165623 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164356 q = 0) : d165614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164356, d165614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14770 q selected
    | true =>
      simp only [d164356, d165614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164357 q = 0) : d165615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164357, d165615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164357, d165615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164360 q = 0) : d165618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164360, d165618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14771 q selected
    | true =>
      simp only [d164360, d165618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164361 q = 0) : d165619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164361, d165619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164361, d165619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164362 q = 0) : d165620 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164362, d165620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164362, d165620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164363 q = 0) : d165621 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164363, d165621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164363, d165621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164364 q = 0) : d165622 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164364, d165622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164364, d165622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164365 q = 0) : d165623 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164365, d165623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164365, d165623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14773 (p : Pattern) (selected : d164369 p = 0) : d165627 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164360 q = 0) : d165618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164360, d165618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14771 q selected
    | true =>
      simp only [d164360, d165618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164361 q = 0) : d165619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164361, d165619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164361, d165619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164366 q = 0) : d165624 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164366, d165624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164366, d165624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164367 q = 0) : d165625 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164367, d165625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164367, d165625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164368 q = 0) : d165626 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164368, d165626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164368, d165626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164369 q = 0) : d165627 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164369, d165627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164369, d165627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14774 (p : Pattern) (selected : d164375 p = 0) : d165633 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164370 q = 0) : d165628 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164370, d165628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14772 q selected
    | true =>
      simp only [d164370, d165628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14773 q selected
  have h2 (q : Pattern) (selected : d164371 q = 0) : d165629 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164371, d165629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164371, d165629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164372 q = 0) : d165630 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164372, d165630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164372, d165630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164373 q = 0) : d165631 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164373, d165631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164373, d165631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164374 q = 0) : d165632 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164374, d165632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164374, d165632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164375 q = 0) : d165633 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164375, d165633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164375, d165633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14775 (p : Pattern) (selected : d164378 p = 0) : d165636 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164356 q = 0) : d165614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164356, d165614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14770 q selected
    | true =>
      simp only [d164356, d165614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164357 q = 0) : d165615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164357, d165615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164357, d165615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164360 q = 0) : d165618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164360, d165618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14771 q selected
    | true =>
      simp only [d164360, d165618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164361 q = 0) : d165619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164361, d165619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164361, d165619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164362 q = 0) : d165620 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164362, d165620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164362, d165620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164363 q = 0) : d165621 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164363, d165621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164363, d165621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164364 q = 0) : d165622 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164364, d165622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164364, d165622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164378 q = 0) : d165636 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164378, d165636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164378, d165636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14776 (p : Pattern) (selected : d164379 p = 0) : d165637 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164360 q = 0) : d165618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164360, d165618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14771 q selected
    | true =>
      simp only [d164360, d165618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164361 q = 0) : d165619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164361, d165619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164361, d165619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164366 q = 0) : d165624 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164366, d165624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164366, d165624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164367 q = 0) : d165625 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164367, d165625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164367, d165625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164368 q = 0) : d165626 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164368, d165626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164368, d165626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164379 q = 0) : d165637 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164379, d165637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164379, d165637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14777 (p : Pattern) (selected : d164385 p = 0) : d165643 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164370 q = 0) : d165628 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164370, d165628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14772 q selected
    | true =>
      simp only [d164370, d165628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14773 q selected
  have h2 (q : Pattern) (selected : d164371 q = 0) : d165629 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164371, d165629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164371, d165629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164372 q = 0) : d165630 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164372, d165630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164372, d165630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164373 q = 0) : d165631 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164373, d165631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164373, d165631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164374 q = 0) : d165632 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164374, d165632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164374, d165632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164380 q = 0) : d165638 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164380, d165638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14775 q selected
    | true =>
      simp only [d164380, d165638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14776 q selected
  have h7 (q : Pattern) (selected : d164381 q = 0) : d165639 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164381, d165639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164381, d165639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164382 q = 0) : d165640 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164382, d165640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164382, d165640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d164383 q = 0) : d165641 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164383, d165641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164383, d165641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164384 q = 0) : d165642 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164384, d165642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164384, d165642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164385 q = 0) : d165643 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164385, d165643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164385, d165643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14778 (p : Pattern) (selected : d164390 p = 0) : d165648 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164356 q = 0) : d165614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164356, d165614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14770 q selected
    | true =>
      simp only [d164356, d165614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164357 q = 0) : d165615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164357, d165615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164357, d165615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164360 q = 0) : d165618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164360, d165618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14771 q selected
    | true =>
      simp only [d164360, d165618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164361 q = 0) : d165619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164361, d165619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164361, d165619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164362 q = 0) : d165620 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164362, d165620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164362, d165620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164363 q = 0) : d165621 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164363, d165621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164363, d165621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164389 q = 0) : d165647 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164389, d165647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164389, d165647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164390 q = 0) : d165648 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164390, d165648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164390, d165648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14779 (p : Pattern) (selected : d164392 p = 0) : d165650 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164360 q = 0) : d165618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164360, d165618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14771 q selected
    | true =>
      simp only [d164360, d165618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164361 q = 0) : d165619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164361, d165619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164361, d165619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164366 q = 0) : d165624 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164366, d165624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164366, d165624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164367 q = 0) : d165625 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164367, d165625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164367, d165625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164391 q = 0) : d165649 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164391, d165649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164391, d165649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164392 q = 0) : d165650 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164392, d165650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164392, d165650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14780 (p : Pattern) (selected : d164399 p = 0) : d165657 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164356 q = 0) : d165614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164356, d165614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14770 q selected
    | true =>
      simp only [d164356, d165614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164357 q = 0) : d165615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164357, d165615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164357, d165615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164360 q = 0) : d165618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164360, d165618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14771 q selected
    | true =>
      simp only [d164360, d165618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164361 q = 0) : d165619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164361, d165619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164361, d165619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164362 q = 0) : d165620 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164362, d165620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164362, d165620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164397 q = 0) : d165655 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164397, d165655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164397, d165655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164398 q = 0) : d165656 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164398, d165656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164398, d165656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164399 q = 0) : d165657 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164399, d165657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164399, d165657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14781 (p : Pattern) (selected : d164402 p = 0) : d165660 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164360 q = 0) : d165618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164360, d165618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14771 q selected
    | true =>
      simp only [d164360, d165618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164361 q = 0) : d165619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164361, d165619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164361, d165619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164366 q = 0) : d165624 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164366, d165624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164366, d165624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164400 q = 0) : d165658 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164400, d165658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164400, d165658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164401 q = 0) : d165659 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164401, d165659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164401, d165659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164402 q = 0) : d165660 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164402, d165660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164402, d165660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14782 (p : Pattern) (selected : d164408 p = 0) : d165666 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1210 q = 0) : d52791 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1210, d52791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro407 q selected
    | true =>
      simp only [d1210, d52791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1211 q = 0) : d52792 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1211, d52792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1211, d52792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d9753 q = 0) : d101274 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9753, d101274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6669 q selected
    | true =>
      simp only [d9753, d101274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9755 q = 0) : d101276 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9755, d101276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9755, d101276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164406 q = 0) : d165664 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164406, d165664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164406, d165664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9763 q = 0) : d101284 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9763, d101284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6670 q selected
    | true =>
      simp only [d9763, d101284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9765 q = 0) : d101286 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9765, d101286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9765, d101286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9778 q = 0) : d101299 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6672 q selected
    | true =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d9780 q = 0) : d101301 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9780, d101301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9780, d101301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d164407 q = 0) : d165665 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164407, d165665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164407, d165665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164408 q = 0) : d165666 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164408, d165666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164408, d165666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14783 (p : Pattern) (selected : d164413 p = 0) : d165671 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9814 q = 0) : d101335 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9814, d101335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6677 q selected
    | true =>
      simp only [d9814, d101335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9816 q = 0) : d101337 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9816, d101337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9816, d101337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d9800 q = 0) : d101321 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6675 q selected
    | true =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9802 q = 0) : d101323 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9802, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164412 q = 0) : d165670 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164412, d165670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164412, d165670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164336 q = 0) : d165594 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164336, d165594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164336, d165594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164413 q = 0) : d165671 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164413, d165671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164413, d165671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro14784 (p : Pattern) (selected : d164419 p = 0) : d165677 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164409 q = 0) : d165667 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164409, d165667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14782 q selected
    | true =>
      simp only [d164409, d165667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14766 q selected
  have h2 (q : Pattern) (selected : d164410 q = 0) : d165668 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164410, d165668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164410, d165668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164411 q = 0) : d165669 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164411, d165669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164411, d165669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164414 q = 0) : d165672 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164414, d165672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14766 q selected
    | true =>
      simp only [d164414, d165672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14783 q selected
  have h5 (q : Pattern) (selected : d164415 q = 0) : d165673 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164415, d165673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164415, d165673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164416 q = 0) : d165674 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164416, d165674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164416, d165674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164417 q = 0) : d165675 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164417, d165675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164417, d165675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164338 q = 0) : d165596 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164338, d165596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14766 q selected
    | true =>
      simp only [d164338, d165596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14767 q selected
  have h9 (q : Pattern) (selected : d164339 q = 0) : d165597 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164339, d165597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164339, d165597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164340 q = 0) : d165598 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164340, d165598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164340, d165598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164344 q = 0) : d165602 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164344, d165602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14767 q selected
    | true =>
      simp only [d164344, d165602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14768 q selected
  have h12 (q : Pattern) (selected : d164345 q = 0) : d165603 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164345, d165603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164345, d165603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d164346 q = 0) : d165604 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164346, d165604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164346, d165604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d164347 q = 0) : d165605 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164347, d165605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164347, d165605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d164418 q = 0) : d165676 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164418, d165676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164418, d165676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d164419 q = 0) : d165677 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164419, d165677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d164419, d165677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro14785 (p : Pattern) (selected : d164424 p = 0) : d165682 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164338 q = 0) : d165596 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164338, d165596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14766 q selected
    | true =>
      simp only [d164338, d165596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14767 q selected
  have h2 (q : Pattern) (selected : d164339 q = 0) : d165597 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164339, d165597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164339, d165597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164340 q = 0) : d165598 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164340, d165598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164340, d165598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164344 q = 0) : d165602 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164344, d165602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14767 q selected
    | true =>
      simp only [d164344, d165602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14768 q selected
  have h5 (q : Pattern) (selected : d164345 q = 0) : d165603 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164345, d165603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164345, d165603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164346 q = 0) : d165604 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164346, d165604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164346, d165604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164347 q = 0) : d165605 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164347, d165605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164347, d165605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164422 q = 0) : d165680 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164422, d165680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164422, d165680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d164423 q = 0) : d165681 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164423, d165681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164423, d165681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164424 q = 0) : d165682 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164424, d165682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d164424, d165682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro14786 (p : Pattern) (selected : d164430 p = 0) : d165688 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164420 q = 0) : d165678 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164420, d165678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14784 q selected
    | true =>
      simp only [d164420, d165678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164421 q = 0) : d165679 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164421, d165679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164421, d165679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164425 q = 0) : d165683 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164425, d165683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14785 q selected
    | true =>
      simp only [d164425, d165683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164426 q = 0) : d165684 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164426, d165684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164426, d165684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164427 q = 0) : d165685 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164427, d165685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164427, d165685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164428 q = 0) : d165686 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164428, d165686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164428, d165686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164429 q = 0) : d165687 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164429, d165687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164429, d165687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164430 q = 0) : d165688 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164430, d165688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164430, d165688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14787 (p : Pattern) (selected : d164434 p = 0) : d165692 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164425 q = 0) : d165683 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164425, d165683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14785 q selected
    | true =>
      simp only [d164425, d165683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164426 q = 0) : d165684 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164426, d165684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164426, d165684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164360 q = 0) : d165618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164360, d165618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14771 q selected
    | true =>
      simp only [d164360, d165618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164361 q = 0) : d165619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164361, d165619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164361, d165619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164431 q = 0) : d165689 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164431, d165689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164431, d165689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164432 q = 0) : d165690 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164432, d165690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164432, d165690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164433 q = 0) : d165691 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164433, d165691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164433, d165691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164434 q = 0) : d165692 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164434, d165692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164434, d165692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14788 (p : Pattern) (selected : d164438 p = 0) : d165592 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1255 q = 0) : d52681 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1255, d52681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro415 q selected
    | true =>
      simp only [d1255, d52681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1256 q = 0) : d52682 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1256, d52682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1256, d52682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d9896 q = 0) : d101310 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9896, d101310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6690 q selected
    | true =>
      simp only [d9896, d101310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9898 q = 0) : d101312 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9898, d101312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9898, d101312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164436 q = 0) : d165590 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164436, d165590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164436, d165590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9908 q = 0) : d101299 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9908, d101299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6691 q selected
    | true =>
      simp only [d9908, d101299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9910 q = 0) : d101301 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9910, d101301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9910, d101301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9918 q = 0) : d101321 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9918, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6692 q selected
    | true =>
      simp only [d9918, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d9920 q = 0) : d101323 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9920, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9920, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d164437 q = 0) : d165591 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164437, d165591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164437, d165591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164438 q = 0) : d165592 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164438, d165592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164438, d165592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14789 (p : Pattern) (selected : d164441 p = 0) : d165595 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1265 q = 0) : d52691 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1265, d52691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro416 q selected
    | true =>
      simp only [d1265, d52691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1266 q = 0) : d52692 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1266, d52692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1266, d52692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1276 q = 0) : d52702 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1276, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro417 q selected
    | true =>
      simp only [d1276, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1277 q = 0) : d52703 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1277, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1277, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164439 q = 0) : d165593 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164439, d165593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164439, d165593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9918 q = 0) : d101321 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9918, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6692 q selected
    | true =>
      simp only [d9918, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9920 q = 0) : d101323 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9920, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9920, d101323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164440 q = 0) : d165594 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164440, d165594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164440, d165594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d164441 q = 0) : d165595 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164441, d165595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164441, d165595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro14790 (p : Pattern) (selected : d164447 p = 0) : d165601 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9943 q = 0) : d69108 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9943, d69108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6695 q selected
    | true =>
      simp only [d9943, d69108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9945 q = 0) : d69109 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9945, d69109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9945, d69109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164445 q = 0) : d165599 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164445, d165599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164445, d165599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9952 q = 0) : d101365 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9952, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6696 q selected
    | true =>
      simp only [d9952, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9954 q = 0) : d101367 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9954, d101367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9954, d101367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164446 q = 0) : d165600 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164446, d165600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164446, d165600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164447 q = 0) : d165601 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164447, d165601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164447, d165601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro14791 (p : Pattern) (selected : d164453 p = 0) : d165607 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1276 q = 0) : d52702 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1276, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro417 q selected
    | true =>
      simp only [d1276, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1277 q = 0) : d52703 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1277, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1277, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164452 q = 0) : d165606 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164452, d165606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164452, d165606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9952 q = 0) : d101365 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9952, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6696 q selected
    | true =>
      simp only [d9952, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9954 q = 0) : d101367 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9954, d101367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9954, d101367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164446 q = 0) : d165600 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164446, d165600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164446, d165600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164453 q = 0) : d165607 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164453, d165607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164453, d165607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro14792 (p : Pattern) (selected : d164459 p = 0) : d165613 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164442 q = 0) : d165596 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164442, d165596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14788 q selected
    | true =>
      simp only [d164442, d165596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14789 q selected
  have h2 (q : Pattern) (selected : d164443 q = 0) : d165597 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164443, d165597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164443, d165597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164444 q = 0) : d165598 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164444, d165598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164444, d165598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164448 q = 0) : d165602 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164448, d165602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14789 q selected
    | true =>
      simp only [d164448, d165602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14790 q selected
  have h5 (q : Pattern) (selected : d164449 q = 0) : d165603 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164449, d165603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164449, d165603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164450 q = 0) : d165604 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164450, d165604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164450, d165604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164451 q = 0) : d165605 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164451, d165605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164451, d165605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164454 q = 0) : d165608 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164454, d165608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14789 q selected
    | true =>
      simp only [d164454, d165608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14791 q selected
  have h9 (q : Pattern) (selected : d164455 q = 0) : d165609 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164455, d165609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164455, d165609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164456 q = 0) : d165610 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164456, d165610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164456, d165610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164457 q = 0) : d165611 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164457, d165611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164457, d165611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d164458 q = 0) : d165612 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164458, d165612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164458, d165612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d164459 q = 0) : d165613 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164459, d165613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d164459, d165613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro14793 (p : Pattern) (selected : d164463 p = 0) : d165617 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164454 q = 0) : d165608 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164454, d165608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14789 q selected
    | true =>
      simp only [d164454, d165608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14791 q selected
  have h2 (q : Pattern) (selected : d164455 q = 0) : d165609 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164455, d165609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164455, d165609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164456 q = 0) : d165610 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164456, d165610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164456, d165610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164457 q = 0) : d165611 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164457, d165611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164457, d165611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164462 q = 0) : d165616 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164462, d165616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164462, d165616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164463 q = 0) : d165617 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164463, d165617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164463, d165617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14794 (p : Pattern) (selected : d164469 p = 0) : d165623 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164460 q = 0) : d165614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164460, d165614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14792 q selected
    | true =>
      simp only [d164460, d165614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164461 q = 0) : d165615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164461, d165615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164461, d165615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164464 q = 0) : d165618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164464, d165618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14793 q selected
    | true =>
      simp only [d164464, d165618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164465 q = 0) : d165619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164465, d165619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164465, d165619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164466 q = 0) : d165620 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164466, d165620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164466, d165620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164467 q = 0) : d165621 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164467, d165621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164467, d165621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164468 q = 0) : d165622 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164468, d165622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164468, d165622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164469 q = 0) : d165623 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164469, d165623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164469, d165623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14795 (p : Pattern) (selected : d164473 p = 0) : d165627 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164464 q = 0) : d165618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164464, d165618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14793 q selected
    | true =>
      simp only [d164464, d165618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164465 q = 0) : d165619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164465, d165619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164465, d165619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164470 q = 0) : d165624 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164470, d165624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164470, d165624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164471 q = 0) : d165625 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164471, d165625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164471, d165625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164472 q = 0) : d165626 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164472, d165626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164472, d165626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164473 q = 0) : d165627 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164473, d165627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164473, d165627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14796 (p : Pattern) (selected : d164476 p = 0) : d165695 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1121 q = 0) : d52702 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro388 q selected
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1122 q = 0) : d52703 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164348 q = 0) : d165606 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164348, d165606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164348, d165606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164476 q = 0) : d165695 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164476, d165695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164476, d165695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro14797 (p : Pattern) (selected : d164482 p = 0) : d165701 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164338 q = 0) : d165596 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164338, d165596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14766 q selected
    | true =>
      simp only [d164338, d165596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14767 q selected
  have h2 (q : Pattern) (selected : d164339 q = 0) : d165597 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164339, d165597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164339, d165597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164340 q = 0) : d165598 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164340, d165598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164340, d165598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164344 q = 0) : d165602 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164344, d165602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14767 q selected
    | true =>
      simp only [d164344, d165602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14768 q selected
  have h5 (q : Pattern) (selected : d164345 q = 0) : d165603 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164345, d165603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164345, d165603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164346 q = 0) : d165604 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164346, d165604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164346, d165604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164347 q = 0) : d165605 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164347, d165605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164347, d165605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164477 q = 0) : d165696 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164477, d165696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14767 q selected
    | true =>
      simp only [d164477, d165696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14796 q selected
  have h9 (q : Pattern) (selected : d164478 q = 0) : d165697 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164478, d165697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164478, d165697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164479 q = 0) : d165698 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164479, d165698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164479, d165698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164480 q = 0) : d165699 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164480, d165699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164480, d165699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d164481 q = 0) : d165700 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164481, d165700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164481, d165700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d164482 q = 0) : d165701 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164482, d165701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d164482, d165701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro14798 (p : Pattern) (selected : d164488 p = 0) : d165707 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164483 q = 0) : d165702 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164483, d165702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14797 q selected
    | true =>
      simp only [d164483, d165702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164484 q = 0) : d165703 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164484, d165703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164484, d165703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164485 q = 0) : d165704 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164485, d165704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164485, d165704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164486 q = 0) : d165705 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164486, d165705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164486, d165705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164487 q = 0) : d165706 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164487, d165706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164487, d165706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164488 q = 0) : d165707 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164488, d165707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164488, d165707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14799 (p : Pattern) (selected : d164494 p = 0) : d165713 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164393 q = 0) : d165651 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164393, d165651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14778 q selected
    | true =>
      simp only [d164393, d165651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14779 q selected
  have h2 (q : Pattern) (selected : d164394 q = 0) : d165652 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164394, d165652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164394, d165652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164395 q = 0) : d165653 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164395, d165653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164395, d165653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164396 q = 0) : d165654 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164396, d165654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164396, d165654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164403 q = 0) : d165661 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164403, d165661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14780 q selected
    | true =>
      simp only [d164403, d165661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14781 q selected
  have h6 (q : Pattern) (selected : d164404 q = 0) : d165662 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164404, d165662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164404, d165662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164405 q = 0) : d165663 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164405, d165663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164405, d165663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164435 q = 0) : d165693 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164435, d165693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14786 q selected
    | true =>
      simp only [d164435, d165693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14787 q selected
  have h9 (q : Pattern) (selected : d164474 q = 0) : d165628 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164474, d165628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14794 q selected
    | true =>
      simp only [d164474, d165628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14795 q selected
  have h10 (q : Pattern) (selected : d164475 q = 0) : d165694 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164475, d165694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d164475, d165694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164489 q = 0) : d165708 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164489, d165708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14798 q selected
    | true =>
      simp only [d164489, d165708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d164490 q = 0) : d165709 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164490, d165709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d164490, d165709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d164491 q = 0) : d165710 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164491, d165710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164491, d165710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d164492 q = 0) : d165711 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164492, d165711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164492, d165711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d164493 q = 0) : d165712 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164493, d165712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164493, d165712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d164494 q = 0) : d165713 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164494, d165713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164494, d165713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro14800 (p : Pattern) (selected : d164495 p = 0) : d165714 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164356 q = 0) : d165614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164356, d165614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14770 q selected
    | true =>
      simp only [d164356, d165614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164357 q = 0) : d165615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164357, d165615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164357, d165615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164360 q = 0) : d165618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164360, d165618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14771 q selected
    | true =>
      simp only [d164360, d165618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164361 q = 0) : d165619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164361, d165619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164361, d165619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164362 q = 0) : d165620 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164362, d165620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164362, d165620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164363 q = 0) : d165621 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164363, d165621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164363, d165621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164389 q = 0) : d165647 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164389, d165647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164389, d165647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164495 q = 0) : d165714 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164495, d165714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164495, d165714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14801 (p : Pattern) (selected : d164496 p = 0) : d165715 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164360 q = 0) : d165618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164360, d165618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14771 q selected
    | true =>
      simp only [d164360, d165618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164361 q = 0) : d165619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164361, d165619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164361, d165619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164366 q = 0) : d165624 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164366, d165624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164366, d165624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164367 q = 0) : d165625 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164367, d165625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164367, d165625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164391 q = 0) : d165649 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164391, d165649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164391, d165649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164496 q = 0) : d165715 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164496, d165715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164496, d165715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14802 (p : Pattern) (selected : d164501 p = 0) : d165720 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164356 q = 0) : d165614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164356, d165614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14770 q selected
    | true =>
      simp only [d164356, d165614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164357 q = 0) : d165615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164357, d165615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164357, d165615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164360 q = 0) : d165618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164360, d165618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14771 q selected
    | true =>
      simp only [d164360, d165618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164361 q = 0) : d165619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164361, d165619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164361, d165619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164362 q = 0) : d165620 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164362, d165620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164362, d165620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164397 q = 0) : d165655 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164397, d165655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164397, d165655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164398 q = 0) : d165656 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164398, d165656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164398, d165656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164501 q = 0) : d165720 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164501, d165720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164501, d165720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14803 (p : Pattern) (selected : d164502 p = 0) : d165721 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164360 q = 0) : d165618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164360, d165618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14771 q selected
    | true =>
      simp only [d164360, d165618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164361 q = 0) : d165619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164361, d165619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164361, d165619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164366 q = 0) : d165624 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164366, d165624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164366, d165624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164400 q = 0) : d165658 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164400, d165658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164400, d165658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164401 q = 0) : d165659 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164401, d165659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164401, d165659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164502 q = 0) : d165721 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164502, d165721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164502, d165721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14804 (p : Pattern) (selected : d164506 p = 0) : d165725 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164420 q = 0) : d165678 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164420, d165678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14784 q selected
    | true =>
      simp only [d164420, d165678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164421 q = 0) : d165679 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164421, d165679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164421, d165679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164425 q = 0) : d165683 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164425, d165683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14785 q selected
    | true =>
      simp only [d164425, d165683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164426 q = 0) : d165684 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164426, d165684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164426, d165684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164427 q = 0) : d165685 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164427, d165685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164427, d165685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164428 q = 0) : d165686 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164428, d165686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164428, d165686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164429 q = 0) : d165687 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164429, d165687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164429, d165687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164506 q = 0) : d165725 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164506, d165725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164506, d165725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14805 (p : Pattern) (selected : d164507 p = 0) : d165726 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164425 q = 0) : d165683 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164425, d165683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14785 q selected
    | true =>
      simp only [d164425, d165683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164426 q = 0) : d165684 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164426, d165684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164426, d165684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164360 q = 0) : d165618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164360, d165618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14771 q selected
    | true =>
      simp only [d164360, d165618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164361 q = 0) : d165619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164361, d165619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164361, d165619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164431 q = 0) : d165689 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164431, d165689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164431, d165689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164432 q = 0) : d165690 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164432, d165690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164432, d165690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164433 q = 0) : d165691 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164433, d165691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164433, d165691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164507 q = 0) : d165726 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164507, d165726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164507, d165726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14806 (p : Pattern) (selected : d164509 p = 0) : d165636 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164460 q = 0) : d165614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164460, d165614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14792 q selected
    | true =>
      simp only [d164460, d165614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164461 q = 0) : d165615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164461, d165615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164461, d165615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164464 q = 0) : d165618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164464, d165618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14793 q selected
    | true =>
      simp only [d164464, d165618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164465 q = 0) : d165619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164465, d165619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164465, d165619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164466 q = 0) : d165620 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164466, d165620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164466, d165620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164467 q = 0) : d165621 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164467, d165621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164467, d165621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164468 q = 0) : d165622 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164468, d165622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164468, d165622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164509 q = 0) : d165636 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164509, d165636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164509, d165636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14807 (p : Pattern) (selected : d164510 p = 0) : d165637 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164464 q = 0) : d165618 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164464, d165618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14793 q selected
    | true =>
      simp only [d164464, d165618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164465 q = 0) : d165619 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164465, d165619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164465, d165619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164470 q = 0) : d165624 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164470, d165624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164470, d165624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164471 q = 0) : d165625 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164471, d165625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164471, d165625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164472 q = 0) : d165626 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164472, d165626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164472, d165626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164510 q = 0) : d165637 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164510, d165637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164510, d165637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14808 (p : Pattern) (selected : d164513 p = 0) : d165729 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164483 q = 0) : d165702 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164483, d165702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14797 q selected
    | true =>
      simp only [d164483, d165702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164484 q = 0) : d165703 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164484, d165703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164484, d165703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164485 q = 0) : d165704 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164485, d165704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164485, d165704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164486 q = 0) : d165705 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164486, d165705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164486, d165705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164487 q = 0) : d165706 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164487, d165706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164487, d165706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164513 q = 0) : d165729 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164513, d165729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164513, d165729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14809 (p : Pattern) (selected : d164519 p = 0) : d165735 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164393 q = 0) : d165651 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164393, d165651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14778 q selected
    | true =>
      simp only [d164393, d165651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14779 q selected
  have h2 (q : Pattern) (selected : d164394 q = 0) : d165652 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164394, d165652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164394, d165652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164395 q = 0) : d165653 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164395, d165653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164395, d165653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164396 q = 0) : d165654 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164396, d165654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164396, d165654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164403 q = 0) : d165661 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164403, d165661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14780 q selected
    | true =>
      simp only [d164403, d165661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14781 q selected
  have h6 (q : Pattern) (selected : d164404 q = 0) : d165662 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164404, d165662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164404, d165662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164405 q = 0) : d165663 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164405, d165663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164405, d165663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164435 q = 0) : d165693 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164435, d165693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14786 q selected
    | true =>
      simp only [d164435, d165693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14787 q selected
  have h9 (q : Pattern) (selected : d164474 q = 0) : d165628 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164474, d165628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14794 q selected
    | true =>
      simp only [d164474, d165628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14795 q selected
  have h10 (q : Pattern) (selected : d164475 q = 0) : d165694 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164475, d165694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d164475, d165694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164489 q = 0) : d165708 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164489, d165708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14798 q selected
    | true =>
      simp only [d164489, d165708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d164490 q = 0) : d165709 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164490, d165709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d164490, d165709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d164491 q = 0) : d165710 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164491, d165710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164491, d165710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d164492 q = 0) : d165711 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164492, d165711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164492, d165711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d164493 q = 0) : d165712 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164493, d165712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164493, d165712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d164497 q = 0) : d165716 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164497, d165716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14800 q selected
    | true =>
      simp only [d164497, d165716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14801 q selected
  have h17 (q : Pattern) (selected : d164498 q = 0) : d165717 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164498, d165717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164498, d165717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d164499 q = 0) : d165718 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164499, d165718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d164499, d165718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d164500 q = 0) : d165719 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164500, d165719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164500, d165719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d164503 q = 0) : d165722 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164503, d165722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14802 q selected
    | true =>
      simp only [d164503, d165722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14803 q selected
  have h21 (q : Pattern) (selected : d164504 q = 0) : d165723 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164504, d165723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164504, d165723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d164505 q = 0) : d165724 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164505, d165724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d164505, d165724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d164508 q = 0) : d165727 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164508, d165727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14804 q selected
    | true =>
      simp only [d164508, d165727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14805 q selected
  have h24 (q : Pattern) (selected : d164511 q = 0) : d165638 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164511, d165638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14806 q selected
    | true =>
      simp only [d164511, d165638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14807 q selected
  have h25 (q : Pattern) (selected : d164512 q = 0) : d165728 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164512, d165728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d164512, d165728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d164514 q = 0) : d165730 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164514, d165730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14808 q selected
    | true =>
      simp only [d164514, d165730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d164515 q = 0) : d165731 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164515, d165731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d164515, d165731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d164516 q = 0) : d165732 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164516, d165732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d164516, d165732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d164517 q = 0) : d165733 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164517, d165733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d164517, d165733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d164518 q = 0) : d165734 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164518, d165734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d164518, d165734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d164519 q = 0) : d165735 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164519, d165735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d164519, d165735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro14810 (p : Pattern) (selected : d164531 p = 0) : d165747 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164521 q = 0) : d165737 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164521, d165737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14787 q selected
    | true =>
      simp only [d164521, d165737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14773 q selected
  have h2 (q : Pattern) (selected : d164522 q = 0) : d165738 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164522, d165738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164522, d165738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164523 q = 0) : d165739 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164523, d165739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164523, d165739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164524 q = 0) : d165740 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164524, d165740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164524, d165740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164525 q = 0) : d165741 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164525, d165741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164525, d165741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164526 q = 0) : d165742 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164526, d165742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14773 q selected
    | true =>
      simp only [d164526, d165742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164527 q = 0) : d165743 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164527, d165743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164527, d165743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164528 q = 0) : d165744 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164528, d165744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164528, d165744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d164529 q = 0) : d165745 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164529, d165745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164529, d165745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164530 q = 0) : d165746 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164530, d165746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164530, d165746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164531 q = 0) : d165747 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164531, d165747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164531, d165747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14811 (p : Pattern) (selected : d164537 p = 0) : d165753 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164526 q = 0) : d165742 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164526, d165742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14773 q selected
    | true =>
      simp only [d164526, d165742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164527 q = 0) : d165743 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164527, d165743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164527, d165743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164528 q = 0) : d165744 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164528, d165744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164528, d165744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164529 q = 0) : d165745 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164529, d165745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164529, d165745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164530 q = 0) : d165746 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164530, d165746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164530, d165746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164532 q = 0) : d165748 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164532, d165748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14776 q selected
    | true =>
      simp only [d164532, d165748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164533 q = 0) : d165749 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164533, d165749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164533, d165749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164534 q = 0) : d165750 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164534, d165750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164534, d165750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d164535 q = 0) : d165751 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164535, d165751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164535, d165751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164536 q = 0) : d165752 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164536, d165752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164536, d165752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164537 q = 0) : d165753 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164537, d165753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164537, d165753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14812 (p : Pattern) (selected : d164544 p = 0) : d165760 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164508 q = 0) : d165727 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164508, d165727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14804 q selected
    | true =>
      simp only [d164508, d165727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14805 q selected
  have h2 (q : Pattern) (selected : d164511 q = 0) : d165638 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164511, d165638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14806 q selected
    | true =>
      simp only [d164511, d165638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14807 q selected
  have h3 (q : Pattern) (selected : d164512 q = 0) : d165728 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164512, d165728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164512, d165728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164514 q = 0) : d165730 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164514, d165730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14808 q selected
    | true =>
      simp only [d164514, d165730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164515 q = 0) : d165731 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164515, d165731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164515, d165731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164516 q = 0) : d165732 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164516, d165732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164516, d165732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164542 q = 0) : d165758 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164542, d165758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164542, d165758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164543 q = 0) : d165759 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164543, d165759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164543, d165759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d164544 q = 0) : d165760 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164544, d165760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164544, d165760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro14813 (p : Pattern) (selected : d164546 p = 0) : d165762 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164532 q = 0) : d165748 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164532, d165748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14776 q selected
    | true =>
      simp only [d164532, d165748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164533 q = 0) : d165749 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164533, d165749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164533, d165749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164534 q = 0) : d165750 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164534, d165750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164534, d165750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164535 q = 0) : d165751 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164535, d165751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164535, d165751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164536 q = 0) : d165752 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164536, d165752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164536, d165752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164546 q = 0) : d165762 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164546, d165762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164546, d165762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14814 (p : Pattern) (selected : d164553 p = 0) : d165769 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164376 q = 0) : d165634 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d164376, d165634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164376, d165634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14774 q selected
  have h2 (q : Pattern) (selected : d164377 q = 0) : d165635 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d164377, d165635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164377, d165635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164386 q = 0) : d165644 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d164386, d165644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14774 q selected
    | true =>
      simp only [d164386, d165644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14777 q selected
  have h4 (q : Pattern) (selected : d164387 q = 0) : d165645 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d164387, d165645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164387, d165645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164388 q = 0) : d165646 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d164388, d165646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164388, d165646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164520 q = 0) : d165736 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d164520, d165736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14799 q selected
    | true =>
      simp only [d164520, d165736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14809 q selected
  have h7 (q : Pattern) (selected : d164538 q = 0) : d165754 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d164538, d165754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14810 q selected
    | true =>
      simp only [d164538, d165754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14811 q selected
  have h8 (q : Pattern) (selected : d164539 q = 0) : d165755 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d164539, d165755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164539, d165755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d164540 q = 0) : d165756 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d164540, d165756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d164540, d165756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d164541 q = 0) : d165757 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d164541, d165757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164541, d165757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164545 q = 0) : d165761 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d164545, d165761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164545, d165761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14812 q selected
  have h12 (q : Pattern) (selected : d164547 q = 0) : d165763 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d164547, d165763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164547, d165763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14813 q selected
  have h13 (q : Pattern) (selected : d164548 q = 0) : d165764 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d164548, d165764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d164548, d165764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d164549 q = 0) : d165765 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d164549, d165765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d164549, d165765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d164550 q = 0) : d165766 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d164550, d165766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d164550, d165766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d164551 q = 0) : d165767 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d164551, d165767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164551, d165767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d164552 q = 0) : d165768 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d164552, d165768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d164552, d165768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d164553 q = 0) : d165769 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d164553, d165769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d164553, d165769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro14815 (p : Pattern) (selected : d164559 p = 0) : d165775 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164554 q = 0) : d165770 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d164554, d165770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164554, d165770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14814 q selected
  have h2 (q : Pattern) (selected : d164555 q = 0) : d165771 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d164555, d165771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164555, d165771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164556 q = 0) : d165772 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d164556, d165772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164556, d165772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164557 q = 0) : d165773 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d164557, d165773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164557, d165773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164558 q = 0) : d165774 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d164558, d165774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164558, d165774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164559 q = 0) : d165775 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d164559, d165775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164559, d165775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14816 (p : Pattern) (selected : d164565 p = 0) : d165781 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1555 q = 0) : d52996 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro466 q selected
    | true =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1556 q = 0) : d52997 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10074 q = 0) : d101501 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10074, d101501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6716 q selected
    | true =>
      simp only [d10074, d101501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10076 q = 0) : d101503 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10076, d101503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10076, d101503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164563 q = 0) : d165779 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164563, d165779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164563, d165779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10063 q = 0) : d101490 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6714 q selected
    | true =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10065 q = 0) : d101492 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10065, d101492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10065, d101492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10085 q = 0) : d101512 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6717 q selected
    | true =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10087 q = 0) : d101514 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d164564 q = 0) : d165780 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164564, d165780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164564, d165780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164565 q = 0) : d165781 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164565, d165781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164565, d165781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14817 (p : Pattern) (selected : d164568 p = 0) : d165784 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1570 q = 0) : d53011 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro469 q selected
    | true =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1571 q = 0) : d53012 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10115 q = 0) : d101542 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10115, d101542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6721 q selected
    | true =>
      simp only [d10115, d101542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10117 q = 0) : d101544 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10117, d101544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10117, d101544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164566 q = 0) : d165782 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164566, d165782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164566, d165782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10085 q = 0) : d101512 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6717 q selected
    | true =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10087 q = 0) : d101514 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164567 q = 0) : d165783 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164567, d165783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164567, d165783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d164568 q = 0) : d165784 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164568, d165784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164568, d165784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro14818 (p : Pattern) (selected : d164574 p = 0) : d165790 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d5134 q = 0) : d69221 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5134, d69221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2814 q selected
    | true =>
      simp only [d5134, d69221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d5135 q = 0) : d69222 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5135, d69222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d5135, d69222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164572 q = 0) : d165788 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164572, d165788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164572, d165788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10135 q = 0) : d101562 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6723 q selected
    | true =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10137 q = 0) : d101564 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164573 q = 0) : d165789 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164573, d165789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164573, d165789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164574 q = 0) : d165790 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164574, d165790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164574, d165790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro14819 (p : Pattern) (selected : d164580 p = 0) : d165796 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1582 q = 0) : d53023 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro470 q selected
    | true =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1583 q = 0) : d53024 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164579 q = 0) : d165795 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164579, d165795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164579, d165795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10135 q = 0) : d101562 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6723 q selected
    | true =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10137 q = 0) : d101564 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164573 q = 0) : d165789 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164573, d165789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164573, d165789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164580 q = 0) : d165796 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164580, d165796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164580, d165796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro14820 (p : Pattern) (selected : d164586 p = 0) : d165802 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164569 q = 0) : d165785 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164569, d165785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14816 q selected
    | true =>
      simp only [d164569, d165785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14817 q selected
  have h2 (q : Pattern) (selected : d164570 q = 0) : d165786 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164570, d165786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164570, d165786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164571 q = 0) : d165787 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164571, d165787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164571, d165787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164575 q = 0) : d165791 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164575, d165791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14817 q selected
    | true =>
      simp only [d164575, d165791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14818 q selected
  have h5 (q : Pattern) (selected : d164576 q = 0) : d165792 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164576, d165792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164576, d165792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164577 q = 0) : d165793 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164577, d165793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164577, d165793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164578 q = 0) : d165794 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164578, d165794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164578, d165794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164581 q = 0) : d165797 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164581, d165797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14817 q selected
    | true =>
      simp only [d164581, d165797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14819 q selected
  have h9 (q : Pattern) (selected : d164582 q = 0) : d165798 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164582, d165798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164582, d165798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164583 q = 0) : d165799 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164583, d165799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164583, d165799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164584 q = 0) : d165800 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164584, d165800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164584, d165800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d164585 q = 0) : d165801 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164585, d165801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164585, d165801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d164586 q = 0) : d165802 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164586, d165802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d164586, d165802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro14821 (p : Pattern) (selected : d164590 p = 0) : d165806 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164581 q = 0) : d165797 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164581, d165797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14817 q selected
    | true =>
      simp only [d164581, d165797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14819 q selected
  have h2 (q : Pattern) (selected : d164582 q = 0) : d165798 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164582, d165798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164582, d165798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164583 q = 0) : d165799 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164583, d165799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164583, d165799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164584 q = 0) : d165800 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164584, d165800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164584, d165800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164589 q = 0) : d165805 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164589, d165805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164589, d165805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164590 q = 0) : d165806 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164590, d165806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164590, d165806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14822 (p : Pattern) (selected : d164596 p = 0) : d165812 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164587 q = 0) : d165803 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164587, d165803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14820 q selected
    | true =>
      simp only [d164587, d165803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164588 q = 0) : d165804 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164588, d165804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164588, d165804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164591 q = 0) : d165807 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164591, d165807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14821 q selected
    | true =>
      simp only [d164591, d165807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164592 q = 0) : d165808 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164592, d165808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164592, d165808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164593 q = 0) : d165809 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164593, d165809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164593, d165809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164594 q = 0) : d165810 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164594, d165810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164594, d165810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164595 q = 0) : d165811 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164595, d165811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164595, d165811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164596 q = 0) : d165812 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164596, d165812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164596, d165812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14823 (p : Pattern) (selected : d164600 p = 0) : d165816 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164591 q = 0) : d165807 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164591, d165807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14821 q selected
    | true =>
      simp only [d164591, d165807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164592 q = 0) : d165808 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164592, d165808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164592, d165808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164597 q = 0) : d165813 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164597, d165813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164597, d165813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164598 q = 0) : d165814 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164598, d165814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164598, d165814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164599 q = 0) : d165815 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164599, d165815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164599, d165815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164600 q = 0) : d165816 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164600, d165816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164600, d165816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14824 (p : Pattern) (selected : d164606 p = 0) : d165822 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164601 q = 0) : d165817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164601, d165817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14822 q selected
    | true =>
      simp only [d164601, d165817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14823 q selected
  have h2 (q : Pattern) (selected : d164602 q = 0) : d165818 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164602, d165818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164602, d165818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164603 q = 0) : d165819 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164603, d165819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164603, d165819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164604 q = 0) : d165820 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164604, d165820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164604, d165820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164605 q = 0) : d165821 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164605, d165821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164605, d165821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164606 q = 0) : d165822 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164606, d165822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164606, d165822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14825 (p : Pattern) (selected : d164609 p = 0) : d165825 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164587 q = 0) : d165803 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164587, d165803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14820 q selected
    | true =>
      simp only [d164587, d165803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164588 q = 0) : d165804 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164588, d165804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164588, d165804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164591 q = 0) : d165807 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164591, d165807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14821 q selected
    | true =>
      simp only [d164591, d165807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164592 q = 0) : d165808 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164592, d165808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164592, d165808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164593 q = 0) : d165809 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164593, d165809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164593, d165809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164594 q = 0) : d165810 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164594, d165810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164594, d165810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164595 q = 0) : d165811 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164595, d165811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164595, d165811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164609 q = 0) : d165825 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164609, d165825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164609, d165825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14826 (p : Pattern) (selected : d164610 p = 0) : d165826 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164591 q = 0) : d165807 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164591, d165807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14821 q selected
    | true =>
      simp only [d164591, d165807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164592 q = 0) : d165808 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164592, d165808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164592, d165808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164597 q = 0) : d165813 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164597, d165813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164597, d165813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164598 q = 0) : d165814 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164598, d165814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164598, d165814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164599 q = 0) : d165815 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164599, d165815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164599, d165815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164610 q = 0) : d165826 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164610, d165826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164610, d165826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14827 (p : Pattern) (selected : d164616 p = 0) : d165832 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164601 q = 0) : d165817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164601, d165817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14822 q selected
    | true =>
      simp only [d164601, d165817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14823 q selected
  have h2 (q : Pattern) (selected : d164602 q = 0) : d165818 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164602, d165818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164602, d165818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164603 q = 0) : d165819 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164603, d165819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164603, d165819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164604 q = 0) : d165820 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164604, d165820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164604, d165820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164605 q = 0) : d165821 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164605, d165821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164605, d165821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164611 q = 0) : d165827 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164611, d165827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14825 q selected
    | true =>
      simp only [d164611, d165827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14826 q selected
  have h7 (q : Pattern) (selected : d164612 q = 0) : d165828 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164612, d165828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164612, d165828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164613 q = 0) : d165829 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164613, d165829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164613, d165829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d164614 q = 0) : d165830 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164614, d165830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164614, d165830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164615 q = 0) : d165831 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164615, d165831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164615, d165831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164616 q = 0) : d165832 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164616, d165832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164616, d165832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14828 (p : Pattern) (selected : d164621 p = 0) : d165837 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164587 q = 0) : d165803 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164587, d165803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14820 q selected
    | true =>
      simp only [d164587, d165803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164588 q = 0) : d165804 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164588, d165804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164588, d165804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164591 q = 0) : d165807 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164591, d165807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14821 q selected
    | true =>
      simp only [d164591, d165807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164592 q = 0) : d165808 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164592, d165808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164592, d165808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164593 q = 0) : d165809 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164593, d165809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164593, d165809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164594 q = 0) : d165810 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164594, d165810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164594, d165810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164620 q = 0) : d165836 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164620, d165836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164620, d165836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164621 q = 0) : d165837 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164621, d165837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164621, d165837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14829 (p : Pattern) (selected : d164623 p = 0) : d165839 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164591 q = 0) : d165807 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164591, d165807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14821 q selected
    | true =>
      simp only [d164591, d165807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164592 q = 0) : d165808 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164592, d165808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164592, d165808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164597 q = 0) : d165813 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164597, d165813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164597, d165813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164598 q = 0) : d165814 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164598, d165814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164598, d165814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164622 q = 0) : d165838 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164622, d165838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164622, d165838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164623 q = 0) : d165839 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164623, d165839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164623, d165839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14830 (p : Pattern) (selected : d164630 p = 0) : d165846 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164587 q = 0) : d165803 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164587, d165803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14820 q selected
    | true =>
      simp only [d164587, d165803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164588 q = 0) : d165804 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164588, d165804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164588, d165804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164591 q = 0) : d165807 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164591, d165807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14821 q selected
    | true =>
      simp only [d164591, d165807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164592 q = 0) : d165808 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164592, d165808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164592, d165808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164593 q = 0) : d165809 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164593, d165809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164593, d165809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164628 q = 0) : d165844 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164628, d165844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164628, d165844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164629 q = 0) : d165845 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164629, d165845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164629, d165845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164630 q = 0) : d165846 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164630, d165846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164630, d165846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14831 (p : Pattern) (selected : d164633 p = 0) : d165849 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164591 q = 0) : d165807 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164591, d165807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14821 q selected
    | true =>
      simp only [d164591, d165807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164592 q = 0) : d165808 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164592, d165808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164592, d165808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164597 q = 0) : d165813 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164597, d165813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164597, d165813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164631 q = 0) : d165847 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164631, d165847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164631, d165847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164632 q = 0) : d165848 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164632, d165848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164632, d165848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164633 q = 0) : d165849 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164633, d165849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164633, d165849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14832 (p : Pattern) (selected : d164639 p = 0) : d165855 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1665 q = 0) : d53106 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1665, d53106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro487 q selected
    | true =>
      simp only [d1665, d53106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1666 q = 0) : d53107 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1666, d53107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1666, d53107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10036 q = 0) : d101463 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, d101463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6711 q selected
    | true =>
      simp only [d10036, d101463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10038 q = 0) : d101465 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10038, d101465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10038, d101465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164637 q = 0) : d165853 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164637, d165853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164637, d165853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10046 q = 0) : d101473 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10046, d101473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6712 q selected
    | true =>
      simp only [d10046, d101473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10048 q = 0) : d101475 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10048, d101475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10048, d101475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10063 q = 0) : d101490 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6714 q selected
    | true =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10065 q = 0) : d101492 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10065, d101492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10065, d101492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d164638 q = 0) : d165854 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164638, d165854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164638, d165854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164639 q = 0) : d165855 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164639, d165855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164639, d165855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14833 (p : Pattern) (selected : d164644 p = 0) : d165860 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10099 q = 0) : d101526 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10099, d101526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6719 q selected
    | true =>
      simp only [d10099, d101526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10101 q = 0) : d101528 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10101, d101528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10101, d101528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10085 q = 0) : d101512 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6717 q selected
    | true =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10087 q = 0) : d101514 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164643 q = 0) : d165859 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164643, d165859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164643, d165859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164567 q = 0) : d165783 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164567, d165783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164567, d165783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164644 q = 0) : d165860 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164644, d165860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164644, d165860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro14834 (p : Pattern) (selected : d164650 p = 0) : d165866 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164640 q = 0) : d165856 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164640, d165856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14832 q selected
    | true =>
      simp only [d164640, d165856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14816 q selected
  have h2 (q : Pattern) (selected : d164641 q = 0) : d165857 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164641, d165857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164641, d165857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164642 q = 0) : d165858 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164642, d165858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164642, d165858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164645 q = 0) : d165861 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164645, d165861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14816 q selected
    | true =>
      simp only [d164645, d165861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14833 q selected
  have h5 (q : Pattern) (selected : d164646 q = 0) : d165862 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164646, d165862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164646, d165862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164647 q = 0) : d165863 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164647, d165863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164647, d165863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164648 q = 0) : d165864 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164648, d165864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164648, d165864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164569 q = 0) : d165785 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164569, d165785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14816 q selected
    | true =>
      simp only [d164569, d165785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14817 q selected
  have h9 (q : Pattern) (selected : d164570 q = 0) : d165786 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164570, d165786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164570, d165786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164571 q = 0) : d165787 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164571, d165787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164571, d165787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164575 q = 0) : d165791 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164575, d165791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14817 q selected
    | true =>
      simp only [d164575, d165791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14818 q selected
  have h12 (q : Pattern) (selected : d164576 q = 0) : d165792 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164576, d165792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164576, d165792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d164577 q = 0) : d165793 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164577, d165793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164577, d165793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d164578 q = 0) : d165794 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164578, d165794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164578, d165794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d164649 q = 0) : d165865 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164649, d165865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164649, d165865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d164650 q = 0) : d165866 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164650, d165866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d164650, d165866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro14835 (p : Pattern) (selected : d164655 p = 0) : d165871 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164569 q = 0) : d165785 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164569, d165785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14816 q selected
    | true =>
      simp only [d164569, d165785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14817 q selected
  have h2 (q : Pattern) (selected : d164570 q = 0) : d165786 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164570, d165786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164570, d165786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164571 q = 0) : d165787 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164571, d165787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164571, d165787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164575 q = 0) : d165791 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164575, d165791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14817 q selected
    | true =>
      simp only [d164575, d165791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14818 q selected
  have h5 (q : Pattern) (selected : d164576 q = 0) : d165792 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164576, d165792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164576, d165792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164577 q = 0) : d165793 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164577, d165793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164577, d165793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164578 q = 0) : d165794 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164578, d165794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164578, d165794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164653 q = 0) : d165869 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164653, d165869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164653, d165869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d164654 q = 0) : d165870 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164654, d165870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164654, d165870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164655 q = 0) : d165871 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164655, d165871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d164655, d165871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro14836 (p : Pattern) (selected : d164661 p = 0) : d165877 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164651 q = 0) : d165867 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164651, d165867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14834 q selected
    | true =>
      simp only [d164651, d165867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164652 q = 0) : d165868 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164652, d165868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164652, d165868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164656 q = 0) : d165872 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164656, d165872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14835 q selected
    | true =>
      simp only [d164656, d165872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164657 q = 0) : d165873 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164657, d165873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164657, d165873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164658 q = 0) : d165874 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164658, d165874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164658, d165874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164659 q = 0) : d165875 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164659, d165875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164659, d165875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164660 q = 0) : d165876 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164660, d165876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164660, d165876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164661 q = 0) : d165877 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164661, d165877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164661, d165877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14837 (p : Pattern) (selected : d164665 p = 0) : d165881 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164656 q = 0) : d165872 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164656, d165872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14835 q selected
    | true =>
      simp only [d164656, d165872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164657 q = 0) : d165873 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164657, d165873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164657, d165873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164591 q = 0) : d165807 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164591, d165807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14821 q selected
    | true =>
      simp only [d164591, d165807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164592 q = 0) : d165808 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164592, d165808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164592, d165808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164662 q = 0) : d165878 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164662, d165878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164662, d165878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164663 q = 0) : d165879 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164663, d165879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164663, d165879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164664 q = 0) : d165880 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164664, d165880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164664, d165880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164665 q = 0) : d165881 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164665, d165881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164665, d165881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14838 (p : Pattern) (selected : d164669 p = 0) : d165781 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1726 q = 0) : d52996 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1726, d52996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro499 q selected
    | true =>
      simp only [d1726, d52996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1727 q = 0) : d52997 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1727, d52997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1727, d52997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10190 q = 0) : d101501 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10190, d101501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6733 q selected
    | true =>
      simp only [d10190, d101501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10192 q = 0) : d101503 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10192, d101503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10192, d101503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164667 q = 0) : d165779 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164667, d165779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164667, d165779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10200 q = 0) : d101490 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10200, d101490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6734 q selected
    | true =>
      simp only [d10200, d101490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10202 q = 0) : d101492 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10202, d101492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10202, d101492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10215 q = 0) : d101512 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10215, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6735 q selected
    | true =>
      simp only [d10215, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10217 q = 0) : d101514 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10217, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10217, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d164668 q = 0) : d165780 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164668, d165780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164668, d165780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164669 q = 0) : d165781 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164669, d165781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164669, d165781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14839 (p : Pattern) (selected : d164672 p = 0) : d165784 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1741 q = 0) : d53011 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1741, d53011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro502 q selected
    | true =>
      simp only [d1741, d53011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1742 q = 0) : d53012 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1742, d53012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1742, d53012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10226 q = 0) : d101542 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10226, d101542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6737 q selected
    | true =>
      simp only [d10226, d101542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10228 q = 0) : d101544 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10228, d101544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10228, d101544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164670 q = 0) : d165782 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164670, d165782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164670, d165782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10215 q = 0) : d101512 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10215, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6735 q selected
    | true =>
      simp only [d10215, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10217 q = 0) : d101514 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10217, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10217, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164671 q = 0) : d165783 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164671, d165783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164671, d165783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d164672 q = 0) : d165784 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164672, d165784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164672, d165784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro14840 (p : Pattern) (selected : d164678 p = 0) : d165790 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10243 q = 0) : d69221 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10243, d69221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6739 q selected
    | true =>
      simp only [d10243, d69221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10245 q = 0) : d69222 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10245, d69222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10245, d69222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164676 q = 0) : d165788 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164676, d165788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164676, d165788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10255 q = 0) : d101562 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10255, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6740 q selected
    | true =>
      simp only [d10255, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10257 q = 0) : d101564 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10257, d101564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10257, d101564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164677 q = 0) : d165789 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164677, d165789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164677, d165789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164678 q = 0) : d165790 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164678, d165790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164678, d165790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro14841 (p : Pattern) (selected : d164684 p = 0) : d165796 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1753 q = 0) : d53023 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1753, d53023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro503 q selected
    | true =>
      simp only [d1753, d53023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1754 q = 0) : d53024 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1754, d53024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1754, d53024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164683 q = 0) : d165795 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164683, d165795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164683, d165795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10255 q = 0) : d101562 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10255, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6740 q selected
    | true =>
      simp only [d10255, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10257 q = 0) : d101564 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10257, d101564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10257, d101564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164677 q = 0) : d165789 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164677, d165789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164677, d165789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164684 q = 0) : d165796 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164684, d165796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164684, d165796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro14842 (p : Pattern) (selected : d164690 p = 0) : d165802 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164673 q = 0) : d165785 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164673, d165785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14838 q selected
    | true =>
      simp only [d164673, d165785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14839 q selected
  have h2 (q : Pattern) (selected : d164674 q = 0) : d165786 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164674, d165786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164674, d165786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164675 q = 0) : d165787 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164675, d165787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164675, d165787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164679 q = 0) : d165791 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164679, d165791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14839 q selected
    | true =>
      simp only [d164679, d165791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14840 q selected
  have h5 (q : Pattern) (selected : d164680 q = 0) : d165792 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164680, d165792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164680, d165792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164681 q = 0) : d165793 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164681, d165793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164681, d165793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164682 q = 0) : d165794 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164682, d165794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164682, d165794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164685 q = 0) : d165797 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164685, d165797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14839 q selected
    | true =>
      simp only [d164685, d165797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14841 q selected
  have h9 (q : Pattern) (selected : d164686 q = 0) : d165798 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164686, d165798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164686, d165798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164687 q = 0) : d165799 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164687, d165799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164687, d165799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164688 q = 0) : d165800 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164688, d165800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164688, d165800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d164689 q = 0) : d165801 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164689, d165801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164689, d165801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d164690 q = 0) : d165802 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164690, d165802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d164690, d165802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro14843 (p : Pattern) (selected : d164694 p = 0) : d165806 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164685 q = 0) : d165797 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164685, d165797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14839 q selected
    | true =>
      simp only [d164685, d165797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14841 q selected
  have h2 (q : Pattern) (selected : d164686 q = 0) : d165798 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164686, d165798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164686, d165798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164687 q = 0) : d165799 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164687, d165799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164687, d165799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164688 q = 0) : d165800 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164688, d165800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164688, d165800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164693 q = 0) : d165805 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164693, d165805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164693, d165805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164694 q = 0) : d165806 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164694, d165806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164694, d165806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14844 (p : Pattern) (selected : d164700 p = 0) : d165812 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164691 q = 0) : d165803 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164691, d165803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14842 q selected
    | true =>
      simp only [d164691, d165803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164692 q = 0) : d165804 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164692, d165804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164692, d165804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164695 q = 0) : d165807 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164695, d165807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14843 q selected
    | true =>
      simp only [d164695, d165807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164696 q = 0) : d165808 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164696, d165808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164696, d165808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164697 q = 0) : d165809 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164697, d165809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164697, d165809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164698 q = 0) : d165810 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164698, d165810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164698, d165810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164699 q = 0) : d165811 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164699, d165811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164699, d165811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164700 q = 0) : d165812 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164700, d165812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164700, d165812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14845 (p : Pattern) (selected : d164704 p = 0) : d165816 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164695 q = 0) : d165807 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164695, d165807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14843 q selected
    | true =>
      simp only [d164695, d165807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164696 q = 0) : d165808 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164696, d165808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164696, d165808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164701 q = 0) : d165813 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164701, d165813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164701, d165813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164702 q = 0) : d165814 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164702, d165814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164702, d165814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164703 q = 0) : d165815 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164703, d165815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164703, d165815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164704 q = 0) : d165816 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164704, d165816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164704, d165816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14846 (p : Pattern) (selected : d164707 p = 0) : d165884 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1582 q = 0) : d53023 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro470 q selected
    | true =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1583 q = 0) : d53024 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164579 q = 0) : d165795 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164579, d165795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164579, d165795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164707 q = 0) : d165884 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164707, d165884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164707, d165884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro14847 (p : Pattern) (selected : d164713 p = 0) : d165890 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164569 q = 0) : d165785 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164569, d165785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14816 q selected
    | true =>
      simp only [d164569, d165785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14817 q selected
  have h2 (q : Pattern) (selected : d164570 q = 0) : d165786 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164570, d165786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164570, d165786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164571 q = 0) : d165787 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164571, d165787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164571, d165787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164575 q = 0) : d165791 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164575, d165791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14817 q selected
    | true =>
      simp only [d164575, d165791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14818 q selected
  have h5 (q : Pattern) (selected : d164576 q = 0) : d165792 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164576, d165792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164576, d165792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164577 q = 0) : d165793 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164577, d165793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164577, d165793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164578 q = 0) : d165794 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164578, d165794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164578, d165794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164708 q = 0) : d165885 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164708, d165885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14817 q selected
    | true =>
      simp only [d164708, d165885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14846 q selected
  have h9 (q : Pattern) (selected : d164709 q = 0) : d165886 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164709, d165886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164709, d165886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164710 q = 0) : d165887 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164710, d165887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164710, d165887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164711 q = 0) : d165888 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164711, d165888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164711, d165888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d164712 q = 0) : d165889 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164712, d165889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164712, d165889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d164713 q = 0) : d165890 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164713, d165890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d164713, d165890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro14848 (p : Pattern) (selected : d164719 p = 0) : d165896 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164714 q = 0) : d165891 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164714, d165891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14847 q selected
    | true =>
      simp only [d164714, d165891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164715 q = 0) : d165892 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164715, d165892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164715, d165892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164716 q = 0) : d165893 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164716, d165893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164716, d165893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164717 q = 0) : d165894 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164717, d165894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164717, d165894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164718 q = 0) : d165895 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164718, d165895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164718, d165895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164719 q = 0) : d165896 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164719, d165896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164719, d165896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14849 (p : Pattern) (selected : d164725 p = 0) : d165902 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164624 q = 0) : d165840 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164624, d165840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14828 q selected
    | true =>
      simp only [d164624, d165840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14829 q selected
  have h2 (q : Pattern) (selected : d164625 q = 0) : d165841 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164625, d165841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164625, d165841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164626 q = 0) : d165842 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164626, d165842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164626, d165842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164627 q = 0) : d165843 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164627, d165843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164627, d165843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164634 q = 0) : d165850 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164634, d165850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14830 q selected
    | true =>
      simp only [d164634, d165850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14831 q selected
  have h6 (q : Pattern) (selected : d164635 q = 0) : d165851 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164635, d165851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164635, d165851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164636 q = 0) : d165852 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164636, d165852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164636, d165852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164666 q = 0) : d165882 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164666, d165882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14836 q selected
    | true =>
      simp only [d164666, d165882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14837 q selected
  have h9 (q : Pattern) (selected : d164705 q = 0) : d165817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164705, d165817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14844 q selected
    | true =>
      simp only [d164705, d165817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14845 q selected
  have h10 (q : Pattern) (selected : d164706 q = 0) : d165883 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164706, d165883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d164706, d165883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164720 q = 0) : d165897 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164720, d165897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14848 q selected
    | true =>
      simp only [d164720, d165897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d164721 q = 0) : d165898 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164721, d165898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d164721, d165898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d164722 q = 0) : d165899 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164722, d165899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164722, d165899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d164723 q = 0) : d165900 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164723, d165900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164723, d165900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d164724 q = 0) : d165901 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164724, d165901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164724, d165901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d164725 q = 0) : d165902 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164725, d165902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164725, d165902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro14850 (p : Pattern) (selected : d164726 p = 0) : d165903 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164587 q = 0) : d165803 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164587, d165803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14820 q selected
    | true =>
      simp only [d164587, d165803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164588 q = 0) : d165804 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164588, d165804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164588, d165804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164591 q = 0) : d165807 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164591, d165807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14821 q selected
    | true =>
      simp only [d164591, d165807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164592 q = 0) : d165808 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164592, d165808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164592, d165808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164593 q = 0) : d165809 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164593, d165809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164593, d165809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164594 q = 0) : d165810 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164594, d165810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164594, d165810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164620 q = 0) : d165836 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164620, d165836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164620, d165836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164726 q = 0) : d165903 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164726, d165903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164726, d165903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14851 (p : Pattern) (selected : d164727 p = 0) : d165904 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164591 q = 0) : d165807 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164591, d165807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14821 q selected
    | true =>
      simp only [d164591, d165807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164592 q = 0) : d165808 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164592, d165808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164592, d165808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164597 q = 0) : d165813 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164597, d165813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164597, d165813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164598 q = 0) : d165814 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164598, d165814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164598, d165814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164622 q = 0) : d165838 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164622, d165838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164622, d165838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164727 q = 0) : d165904 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164727, d165904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164727, d165904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14852 (p : Pattern) (selected : d164732 p = 0) : d165909 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164587 q = 0) : d165803 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164587, d165803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14820 q selected
    | true =>
      simp only [d164587, d165803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164588 q = 0) : d165804 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164588, d165804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164588, d165804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164591 q = 0) : d165807 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164591, d165807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14821 q selected
    | true =>
      simp only [d164591, d165807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164592 q = 0) : d165808 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164592, d165808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164592, d165808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164593 q = 0) : d165809 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164593, d165809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164593, d165809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164628 q = 0) : d165844 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164628, d165844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164628, d165844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164629 q = 0) : d165845 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164629, d165845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164629, d165845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164732 q = 0) : d165909 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164732, d165909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164732, d165909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14853 (p : Pattern) (selected : d164733 p = 0) : d165910 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164591 q = 0) : d165807 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164591, d165807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14821 q selected
    | true =>
      simp only [d164591, d165807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164592 q = 0) : d165808 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164592, d165808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164592, d165808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164597 q = 0) : d165813 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164597, d165813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164597, d165813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164631 q = 0) : d165847 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164631, d165847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164631, d165847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164632 q = 0) : d165848 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164632, d165848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164632, d165848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164733 q = 0) : d165910 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164733, d165910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164733, d165910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14854 (p : Pattern) (selected : d164737 p = 0) : d165914 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164651 q = 0) : d165867 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164651, d165867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14834 q selected
    | true =>
      simp only [d164651, d165867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164652 q = 0) : d165868 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164652, d165868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164652, d165868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164656 q = 0) : d165872 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164656, d165872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14835 q selected
    | true =>
      simp only [d164656, d165872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164657 q = 0) : d165873 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164657, d165873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164657, d165873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164658 q = 0) : d165874 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164658, d165874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164658, d165874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164659 q = 0) : d165875 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164659, d165875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164659, d165875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164660 q = 0) : d165876 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164660, d165876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164660, d165876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164737 q = 0) : d165914 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164737, d165914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164737, d165914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14855 (p : Pattern) (selected : d164738 p = 0) : d165915 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164656 q = 0) : d165872 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164656, d165872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14835 q selected
    | true =>
      simp only [d164656, d165872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164657 q = 0) : d165873 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164657, d165873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164657, d165873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164591 q = 0) : d165807 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164591, d165807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14821 q selected
    | true =>
      simp only [d164591, d165807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164592 q = 0) : d165808 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164592, d165808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164592, d165808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164662 q = 0) : d165878 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164662, d165878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164662, d165878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164663 q = 0) : d165879 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164663, d165879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164663, d165879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164664 q = 0) : d165880 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164664, d165880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164664, d165880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164738 q = 0) : d165915 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164738, d165915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164738, d165915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14856 (p : Pattern) (selected : d164740 p = 0) : d165825 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164691 q = 0) : d165803 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164691, d165803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14842 q selected
    | true =>
      simp only [d164691, d165803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164692 q = 0) : d165804 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164692, d165804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164692, d165804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164695 q = 0) : d165807 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164695, d165807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14843 q selected
    | true =>
      simp only [d164695, d165807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164696 q = 0) : d165808 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164696, d165808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164696, d165808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164697 q = 0) : d165809 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164697, d165809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164697, d165809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164698 q = 0) : d165810 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164698, d165810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164698, d165810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164699 q = 0) : d165811 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164699, d165811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164699, d165811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164740 q = 0) : d165825 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164740, d165825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164740, d165825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14857 (p : Pattern) (selected : d164741 p = 0) : d165826 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164695 q = 0) : d165807 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164695, d165807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14843 q selected
    | true =>
      simp only [d164695, d165807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164696 q = 0) : d165808 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164696, d165808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164696, d165808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164701 q = 0) : d165813 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164701, d165813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164701, d165813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164702 q = 0) : d165814 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164702, d165814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164702, d165814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164703 q = 0) : d165815 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164703, d165815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164703, d165815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164741 q = 0) : d165826 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164741, d165826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164741, d165826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14858 (p : Pattern) (selected : d164744 p = 0) : d165918 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164714 q = 0) : d165891 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164714, d165891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14847 q selected
    | true =>
      simp only [d164714, d165891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164715 q = 0) : d165892 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164715, d165892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164715, d165892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164716 q = 0) : d165893 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164716, d165893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164716, d165893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164717 q = 0) : d165894 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164717, d165894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164717, d165894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164718 q = 0) : d165895 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164718, d165895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164718, d165895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164744 q = 0) : d165918 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164744, d165918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164744, d165918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14859 (p : Pattern) (selected : d164750 p = 0) : d165924 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164624 q = 0) : d165840 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164624, d165840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14828 q selected
    | true =>
      simp only [d164624, d165840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14829 q selected
  have h2 (q : Pattern) (selected : d164625 q = 0) : d165841 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164625, d165841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164625, d165841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164626 q = 0) : d165842 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164626, d165842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164626, d165842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164627 q = 0) : d165843 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164627, d165843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164627, d165843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164634 q = 0) : d165850 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164634, d165850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14830 q selected
    | true =>
      simp only [d164634, d165850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14831 q selected
  have h6 (q : Pattern) (selected : d164635 q = 0) : d165851 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164635, d165851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164635, d165851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164636 q = 0) : d165852 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164636, d165852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164636, d165852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164666 q = 0) : d165882 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164666, d165882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14836 q selected
    | true =>
      simp only [d164666, d165882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14837 q selected
  have h9 (q : Pattern) (selected : d164705 q = 0) : d165817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164705, d165817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14844 q selected
    | true =>
      simp only [d164705, d165817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14845 q selected
  have h10 (q : Pattern) (selected : d164706 q = 0) : d165883 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164706, d165883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d164706, d165883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164720 q = 0) : d165897 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164720, d165897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14848 q selected
    | true =>
      simp only [d164720, d165897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d164721 q = 0) : d165898 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164721, d165898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d164721, d165898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d164722 q = 0) : d165899 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164722, d165899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164722, d165899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d164723 q = 0) : d165900 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164723, d165900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164723, d165900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d164724 q = 0) : d165901 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164724, d165901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164724, d165901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d164728 q = 0) : d165905 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164728, d165905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14850 q selected
    | true =>
      simp only [d164728, d165905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14851 q selected
  have h17 (q : Pattern) (selected : d164729 q = 0) : d165906 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164729, d165906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164729, d165906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d164730 q = 0) : d165907 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164730, d165907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d164730, d165907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d164731 q = 0) : d165908 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164731, d165908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164731, d165908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d164734 q = 0) : d165911 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164734, d165911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14852 q selected
    | true =>
      simp only [d164734, d165911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14853 q selected
  have h21 (q : Pattern) (selected : d164735 q = 0) : d165912 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164735, d165912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164735, d165912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d164736 q = 0) : d165913 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164736, d165913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d164736, d165913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d164739 q = 0) : d165916 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164739, d165916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14854 q selected
    | true =>
      simp only [d164739, d165916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14855 q selected
  have h24 (q : Pattern) (selected : d164742 q = 0) : d165827 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164742, d165827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14856 q selected
    | true =>
      simp only [d164742, d165827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14857 q selected
  have h25 (q : Pattern) (selected : d164743 q = 0) : d165917 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164743, d165917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d164743, d165917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d164745 q = 0) : d165919 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164745, d165919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14858 q selected
    | true =>
      simp only [d164745, d165919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d164746 q = 0) : d165920 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164746, d165920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d164746, d165920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d164747 q = 0) : d165921 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164747, d165921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d164747, d165921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d164748 q = 0) : d165922 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164748, d165922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d164748, d165922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d164749 q = 0) : d165923 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164749, d165923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d164749, d165923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d164750 q = 0) : d165924 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164750, d165924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d164750, d165924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro14860 (p : Pattern) (selected : d164762 p = 0) : d165936 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164752 q = 0) : d165926 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164752, d165926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14837 q selected
    | true =>
      simp only [d164752, d165926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14823 q selected
  have h2 (q : Pattern) (selected : d164753 q = 0) : d165927 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164753, d165927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164753, d165927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164754 q = 0) : d165928 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164754, d165928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164754, d165928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164755 q = 0) : d165929 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164755, d165929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164755, d165929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164756 q = 0) : d165930 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164756, d165930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164756, d165930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164757 q = 0) : d165931 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164757, d165931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14823 q selected
    | true =>
      simp only [d164757, d165931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164758 q = 0) : d165932 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164758, d165932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164758, d165932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164759 q = 0) : d165933 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164759, d165933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164759, d165933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d164760 q = 0) : d165934 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164760, d165934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164760, d165934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164761 q = 0) : d165935 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164761, d165935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164761, d165935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164762 q = 0) : d165936 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164762, d165936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164762, d165936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14861 (p : Pattern) (selected : d164768 p = 0) : d165942 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164757 q = 0) : d165931 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164757, d165931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14823 q selected
    | true =>
      simp only [d164757, d165931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164758 q = 0) : d165932 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164758, d165932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164758, d165932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164759 q = 0) : d165933 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164759, d165933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164759, d165933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164760 q = 0) : d165934 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164760, d165934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164760, d165934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164761 q = 0) : d165935 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164761, d165935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164761, d165935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164763 q = 0) : d165937 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164763, d165937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14826 q selected
    | true =>
      simp only [d164763, d165937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164764 q = 0) : d165938 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164764, d165938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164764, d165938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164765 q = 0) : d165939 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164765, d165939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164765, d165939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d164766 q = 0) : d165940 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164766, d165940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164766, d165940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164767 q = 0) : d165941 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164767, d165941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164767, d165941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164768 q = 0) : d165942 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164768, d165942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164768, d165942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14862 (p : Pattern) (selected : d164775 p = 0) : d165949 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164739 q = 0) : d165916 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164739, d165916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14854 q selected
    | true =>
      simp only [d164739, d165916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14855 q selected
  have h2 (q : Pattern) (selected : d164742 q = 0) : d165827 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164742, d165827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14856 q selected
    | true =>
      simp only [d164742, d165827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14857 q selected
  have h3 (q : Pattern) (selected : d164743 q = 0) : d165917 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164743, d165917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164743, d165917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164745 q = 0) : d165919 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164745, d165919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14858 q selected
    | true =>
      simp only [d164745, d165919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164746 q = 0) : d165920 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164746, d165920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164746, d165920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164747 q = 0) : d165921 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164747, d165921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164747, d165921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164773 q = 0) : d165947 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164773, d165947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164773, d165947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164774 q = 0) : d165948 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164774, d165948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164774, d165948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d164775 q = 0) : d165949 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164775, d165949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164775, d165949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro14863 (p : Pattern) (selected : d164777 p = 0) : d165951 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164763 q = 0) : d165937 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164763, d165937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14826 q selected
    | true =>
      simp only [d164763, d165937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164764 q = 0) : d165938 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164764, d165938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164764, d165938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164765 q = 0) : d165939 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164765, d165939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164765, d165939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164766 q = 0) : d165940 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164766, d165940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164766, d165940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164767 q = 0) : d165941 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164767, d165941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164767, d165941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164777 q = 0) : d165951 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164777, d165951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164777, d165951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14864 (p : Pattern) (selected : d164784 p = 0) : d165958 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164607 q = 0) : d165823 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d164607, d165823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164607, d165823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14824 q selected
  have h2 (q : Pattern) (selected : d164608 q = 0) : d165824 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d164608, d165824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164608, d165824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164617 q = 0) : d165833 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d164617, d165833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14824 q selected
    | true =>
      simp only [d164617, d165833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14827 q selected
  have h4 (q : Pattern) (selected : d164618 q = 0) : d165834 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d164618, d165834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164618, d165834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164619 q = 0) : d165835 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d164619, d165835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164619, d165835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164751 q = 0) : d165925 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d164751, d165925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14849 q selected
    | true =>
      simp only [d164751, d165925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14859 q selected
  have h7 (q : Pattern) (selected : d164769 q = 0) : d165943 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d164769, d165943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14860 q selected
    | true =>
      simp only [d164769, d165943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14861 q selected
  have h8 (q : Pattern) (selected : d164770 q = 0) : d165944 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d164770, d165944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164770, d165944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d164771 q = 0) : d165945 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d164771, d165945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d164771, d165945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d164772 q = 0) : d165946 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d164772, d165946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164772, d165946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164776 q = 0) : d165950 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d164776, d165950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164776, d165950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14862 q selected
  have h12 (q : Pattern) (selected : d164778 q = 0) : d165952 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d164778, d165952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164778, d165952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14863 q selected
  have h13 (q : Pattern) (selected : d164779 q = 0) : d165953 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d164779, d165953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d164779, d165953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d164780 q = 0) : d165954 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d164780, d165954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d164780, d165954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d164781 q = 0) : d165955 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d164781, d165955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d164781, d165955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d164782 q = 0) : d165956 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d164782, d165956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164782, d165956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d164783 q = 0) : d165957 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d164783, d165957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d164783, d165957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d164784 q = 0) : d165958 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d164784, d165958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d164784, d165958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro14865 (p : Pattern) (selected : d164790 p = 0) : d165964 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164785 q = 0) : d165959 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d164785, d165959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164785, d165959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14864 q selected
  have h2 (q : Pattern) (selected : d164786 q = 0) : d165960 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d164786, d165960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164786, d165960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164787 q = 0) : d165961 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d164787, d165961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164787, d165961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164788 q = 0) : d165962 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d164788, d165962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164788, d165962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164789 q = 0) : d165963 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d164789, d165963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164789, d165963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164790 q = 0) : d165964 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d164790, d165964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164790, d165964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14866 (p : Pattern) (selected : d164797 p = 0) : d165971 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2035 q = 0) : d53314 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro553 q selected
    | true =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2036 q = 0) : d53315 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2036, d53315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2036, d53315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10364 q = 0) : d101685 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d101685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6758 q selected
    | true =>
      simp only [d10364, d101685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10366 q = 0) : d101687 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d101687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10366, d101687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164795 q = 0) : d165969 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164795, d165969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164795, d165969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10353 q = 0) : d101674 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6756 q selected
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10355 q = 0) : d101676 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10371 q = 0) : d101692 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6759 q selected
    | true =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10373 q = 0) : d101694 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d164796 q = 0) : d165970 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164796, d165970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164796, d165970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164797 q = 0) : d165971 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164797, d165971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164797, d165971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14867 (p : Pattern) (selected : d164800 p = 0) : d165974 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2053 q = 0) : d53332 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro558 q selected
    | true =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2054 q = 0) : d53333 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10391 q = 0) : d101712 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10391, d101712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6762 q selected
    | true =>
      simp only [d10391, d101712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10393 q = 0) : d101714 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10393, d101714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10393, d101714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164798 q = 0) : d165972 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164798, d165972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164798, d165972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10371 q = 0) : d101692 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6759 q selected
    | true =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10373 q = 0) : d101694 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164799 q = 0) : d165973 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164799, d165973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164799, d165973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d164800 q = 0) : d165974 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164800, d165974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164800, d165974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro14868 (p : Pattern) (selected : d164806 p = 0) : d165980 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d5247 q = 0) : d69331 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5247, d69331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2828 q selected
    | true =>
      simp only [d5247, d69331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d5248 q = 0) : d69332 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5248, d69332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d5248, d69332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164804 q = 0) : d165978 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164804, d165978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164804, d165978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10412 q = 0) : d101733 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6764 q selected
    | true =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10414 q = 0) : d101735 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164805 q = 0) : d165979 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164805, d165979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164805, d165979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164806 q = 0) : d165980 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164806, d165980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164806, d165980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro14869 (p : Pattern) (selected : d164812 p = 0) : d165986 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2065 q = 0) : d53344 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro559 q selected
    | true =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2066 q = 0) : d53345 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164811 q = 0) : d165985 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164811, d165985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164811, d165985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10412 q = 0) : d101733 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6764 q selected
    | true =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10414 q = 0) : d101735 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164805 q = 0) : d165979 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164805, d165979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164805, d165979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164812 q = 0) : d165986 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164812, d165986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164812, d165986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro14870 (p : Pattern) (selected : d164818 p = 0) : d165992 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164801 q = 0) : d165975 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164801, d165975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14866 q selected
    | true =>
      simp only [d164801, d165975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14867 q selected
  have h2 (q : Pattern) (selected : d164802 q = 0) : d165976 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164802, d165976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164802, d165976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164803 q = 0) : d165977 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164803, d165977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164803, d165977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164807 q = 0) : d165981 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164807, d165981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14867 q selected
    | true =>
      simp only [d164807, d165981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14868 q selected
  have h5 (q : Pattern) (selected : d164808 q = 0) : d165982 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164808, d165982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164808, d165982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164809 q = 0) : d165983 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164809, d165983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164809, d165983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164810 q = 0) : d165984 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164810, d165984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164810, d165984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164813 q = 0) : d165987 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164813, d165987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14867 q selected
    | true =>
      simp only [d164813, d165987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14869 q selected
  have h9 (q : Pattern) (selected : d164814 q = 0) : d165988 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164814, d165988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164814, d165988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164815 q = 0) : d165989 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164815, d165989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164815, d165989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164816 q = 0) : d165990 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164816, d165990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164816, d165990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d164817 q = 0) : d165991 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164817, d165991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164817, d165991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d164818 q = 0) : d165992 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164818, d165992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d164818, d165992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro14871 (p : Pattern) (selected : d164822 p = 0) : d165996 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164813 q = 0) : d165987 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164813, d165987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14867 q selected
    | true =>
      simp only [d164813, d165987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14869 q selected
  have h2 (q : Pattern) (selected : d164814 q = 0) : d165988 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164814, d165988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164814, d165988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164815 q = 0) : d165989 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164815, d165989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164815, d165989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164816 q = 0) : d165990 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164816, d165990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164816, d165990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164821 q = 0) : d165995 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164821, d165995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164821, d165995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164822 q = 0) : d165996 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164822, d165996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164822, d165996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14872 (p : Pattern) (selected : d164828 p = 0) : d166002 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164819 q = 0) : d165993 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164819, d165993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14870 q selected
    | true =>
      simp only [d164819, d165993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164820 q = 0) : d165994 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164820, d165994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164820, d165994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164823 q = 0) : d165997 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164823, d165997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14871 q selected
    | true =>
      simp only [d164823, d165997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164824 q = 0) : d165998 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164824, d165998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164824, d165998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164825 q = 0) : d165999 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164825, d165999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164825, d165999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164826 q = 0) : d166000 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164826, d166000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164826, d166000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164827 q = 0) : d166001 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164827, d166001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164827, d166001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164828 q = 0) : d166002 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164828, d166002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164828, d166002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14873 (p : Pattern) (selected : d164832 p = 0) : d166006 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164823 q = 0) : d165997 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164823, d165997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14871 q selected
    | true =>
      simp only [d164823, d165997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164824 q = 0) : d165998 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164824, d165998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164824, d165998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164829 q = 0) : d166003 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164829, d166003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164829, d166003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164830 q = 0) : d166004 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164830, d166004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164830, d166004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164831 q = 0) : d166005 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164831, d166005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164831, d166005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164832 q = 0) : d166006 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164832, d166006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164832, d166006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14874 (p : Pattern) (selected : d164838 p = 0) : d166012 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164833 q = 0) : d166007 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164833, d166007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14872 q selected
    | true =>
      simp only [d164833, d166007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14873 q selected
  have h2 (q : Pattern) (selected : d164834 q = 0) : d166008 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164834, d166008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164834, d166008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164835 q = 0) : d166009 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164835, d166009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164835, d166009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164836 q = 0) : d166010 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164836, d166010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164836, d166010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164837 q = 0) : d166011 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164837, d166011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164837, d166011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164838 q = 0) : d166012 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164838, d166012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164838, d166012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14875 (p : Pattern) (selected : d164841 p = 0) : d166015 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164819 q = 0) : d165993 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164819, d165993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14870 q selected
    | true =>
      simp only [d164819, d165993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164820 q = 0) : d165994 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164820, d165994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164820, d165994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164823 q = 0) : d165997 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164823, d165997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14871 q selected
    | true =>
      simp only [d164823, d165997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164824 q = 0) : d165998 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164824, d165998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164824, d165998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164825 q = 0) : d165999 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164825, d165999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164825, d165999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164826 q = 0) : d166000 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164826, d166000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164826, d166000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164827 q = 0) : d166001 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164827, d166001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164827, d166001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164841 q = 0) : d166015 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164841, d166015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164841, d166015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14876 (p : Pattern) (selected : d164842 p = 0) : d166016 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164823 q = 0) : d165997 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164823, d165997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14871 q selected
    | true =>
      simp only [d164823, d165997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164824 q = 0) : d165998 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164824, d165998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164824, d165998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164829 q = 0) : d166003 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164829, d166003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164829, d166003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164830 q = 0) : d166004 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164830, d166004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164830, d166004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164831 q = 0) : d166005 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164831, d166005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164831, d166005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164842 q = 0) : d166016 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164842, d166016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164842, d166016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14877 (p : Pattern) (selected : d164848 p = 0) : d166022 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164833 q = 0) : d166007 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164833, d166007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14872 q selected
    | true =>
      simp only [d164833, d166007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14873 q selected
  have h2 (q : Pattern) (selected : d164834 q = 0) : d166008 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164834, d166008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164834, d166008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164835 q = 0) : d166009 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164835, d166009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164835, d166009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164836 q = 0) : d166010 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164836, d166010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164836, d166010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164837 q = 0) : d166011 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164837, d166011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164837, d166011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164843 q = 0) : d166017 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164843, d166017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14875 q selected
    | true =>
      simp only [d164843, d166017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14876 q selected
  have h7 (q : Pattern) (selected : d164844 q = 0) : d166018 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164844, d166018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164844, d166018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164845 q = 0) : d166019 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164845, d166019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164845, d166019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d164846 q = 0) : d166020 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164846, d166020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164846, d166020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164847 q = 0) : d166021 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164847, d166021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164847, d166021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164848 q = 0) : d166022 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164848, d166022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164848, d166022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14878 (p : Pattern) (selected : d164853 p = 0) : d166027 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164819 q = 0) : d165993 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164819, d165993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14870 q selected
    | true =>
      simp only [d164819, d165993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164820 q = 0) : d165994 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164820, d165994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164820, d165994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164823 q = 0) : d165997 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164823, d165997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14871 q selected
    | true =>
      simp only [d164823, d165997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164824 q = 0) : d165998 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164824, d165998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164824, d165998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164825 q = 0) : d165999 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164825, d165999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164825, d165999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164826 q = 0) : d166000 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164826, d166000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164826, d166000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164852 q = 0) : d166026 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164852, d166026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164852, d166026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164853 q = 0) : d166027 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164853, d166027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164853, d166027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14879 (p : Pattern) (selected : d164855 p = 0) : d166029 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164823 q = 0) : d165997 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164823, d165997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14871 q selected
    | true =>
      simp only [d164823, d165997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164824 q = 0) : d165998 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164824, d165998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164824, d165998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164829 q = 0) : d166003 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164829, d166003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164829, d166003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164830 q = 0) : d166004 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164830, d166004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164830, d166004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164854 q = 0) : d166028 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164854, d166028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164854, d166028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164855 q = 0) : d166029 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164855, d166029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164855, d166029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14880 (p : Pattern) (selected : d164862 p = 0) : d166036 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164819 q = 0) : d165993 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164819, d165993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14870 q selected
    | true =>
      simp only [d164819, d165993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164820 q = 0) : d165994 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164820, d165994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164820, d165994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164823 q = 0) : d165997 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164823, d165997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14871 q selected
    | true =>
      simp only [d164823, d165997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164824 q = 0) : d165998 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164824, d165998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164824, d165998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164825 q = 0) : d165999 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164825, d165999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164825, d165999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164860 q = 0) : d166034 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164860, d166034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164860, d166034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164861 q = 0) : d166035 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164861, d166035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164861, d166035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164862 q = 0) : d166036 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164862, d166036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164862, d166036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14881 (p : Pattern) (selected : d164865 p = 0) : d166039 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164823 q = 0) : d165997 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164823, d165997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14871 q selected
    | true =>
      simp only [d164823, d165997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164824 q = 0) : d165998 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164824, d165998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164824, d165998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164829 q = 0) : d166003 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164829, d166003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164829, d166003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164863 q = 0) : d166037 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164863, d166037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164863, d166037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164864 q = 0) : d166038 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164864, d166038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164864, d166038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164865 q = 0) : d166039 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164865, d166039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164865, d166039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14882 (p : Pattern) (selected : d164871 p = 0) : d166045 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2144 q = 0) : d53423 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2144, d53423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro576 q selected
    | true =>
      simp only [d2144, d53423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2145 q = 0) : d53424 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2145, d53424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2145, d53424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10343 q = 0) : d101664 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, d101664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6755 q selected
    | true =>
      simp only [d10343, d101664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10345 q = 0) : d101666 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10345, d101666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10345, d101666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164869 q = 0) : d166043 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164869, d166043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164869, d166043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10353 q = 0) : d101674 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6756 q selected
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10355 q = 0) : d101676 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164870 q = 0) : d166044 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164870, d166044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164870, d166044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d164871 q = 0) : d166045 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164871, d166045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164871, d166045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro14883 (p : Pattern) (selected : d164875 p = 0) : d166049 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10353 q = 0) : d101674 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6756 q selected
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10355 q = 0) : d101676 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10371 q = 0) : d101692 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6759 q selected
    | true =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10373 q = 0) : d101694 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164796 q = 0) : d165970 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164796, d165970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164796, d165970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164799 q = 0) : d165973 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164799, d165973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164799, d165973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164875 q = 0) : d166049 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164875, d166049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164875, d166049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro14884 (p : Pattern) (selected : d164881 p = 0) : d166055 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164872 q = 0) : d166046 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164872, d166046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14882 q selected
    | true =>
      simp only [d164872, d166046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14866 q selected
  have h2 (q : Pattern) (selected : d164873 q = 0) : d166047 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164873, d166047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164873, d166047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164874 q = 0) : d166048 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164874, d166048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164874, d166048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164876 q = 0) : d166050 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164876, d166050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14866 q selected
    | true =>
      simp only [d164876, d166050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14883 q selected
  have h5 (q : Pattern) (selected : d164877 q = 0) : d166051 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164877, d166051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164877, d166051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164878 q = 0) : d166052 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164878, d166052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164878, d166052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164879 q = 0) : d166053 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164879, d166053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164879, d166053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164801 q = 0) : d165975 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164801, d165975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14866 q selected
    | true =>
      simp only [d164801, d165975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14867 q selected
  have h9 (q : Pattern) (selected : d164802 q = 0) : d165976 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164802, d165976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164802, d165976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164803 q = 0) : d165977 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164803, d165977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164803, d165977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164807 q = 0) : d165981 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164807, d165981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14867 q selected
    | true =>
      simp only [d164807, d165981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14868 q selected
  have h12 (q : Pattern) (selected : d164808 q = 0) : d165982 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164808, d165982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164808, d165982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d164809 q = 0) : d165983 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164809, d165983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164809, d165983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d164810 q = 0) : d165984 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164810, d165984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164810, d165984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d164880 q = 0) : d166054 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164880, d166054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164880, d166054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d164881 q = 0) : d166055 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164881, d166055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d164881, d166055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro14885 (p : Pattern) (selected : d164886 p = 0) : d166060 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164801 q = 0) : d165975 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164801, d165975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14866 q selected
    | true =>
      simp only [d164801, d165975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14867 q selected
  have h2 (q : Pattern) (selected : d164802 q = 0) : d165976 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164802, d165976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164802, d165976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164803 q = 0) : d165977 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164803, d165977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164803, d165977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164807 q = 0) : d165981 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164807, d165981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14867 q selected
    | true =>
      simp only [d164807, d165981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14868 q selected
  have h5 (q : Pattern) (selected : d164808 q = 0) : d165982 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164808, d165982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164808, d165982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164809 q = 0) : d165983 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164809, d165983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164809, d165983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164810 q = 0) : d165984 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164810, d165984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164810, d165984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164884 q = 0) : d166058 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164884, d166058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164884, d166058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d164885 q = 0) : d166059 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164885, d166059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164885, d166059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164886 q = 0) : d166060 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164886, d166060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d164886, d166060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro14886 (p : Pattern) (selected : d164892 p = 0) : d166066 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164882 q = 0) : d166056 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164882, d166056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14884 q selected
    | true =>
      simp only [d164882, d166056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164883 q = 0) : d166057 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164883, d166057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164883, d166057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164887 q = 0) : d166061 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164887, d166061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14885 q selected
    | true =>
      simp only [d164887, d166061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164888 q = 0) : d166062 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164888, d166062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164888, d166062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164889 q = 0) : d166063 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164889, d166063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164889, d166063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164890 q = 0) : d166064 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164890, d166064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164890, d166064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164891 q = 0) : d166065 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164891, d166065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164891, d166065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164892 q = 0) : d166066 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164892, d166066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164892, d166066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14887 (p : Pattern) (selected : d164896 p = 0) : d166070 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164887 q = 0) : d166061 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164887, d166061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14885 q selected
    | true =>
      simp only [d164887, d166061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164888 q = 0) : d166062 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164888, d166062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164888, d166062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164823 q = 0) : d165997 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164823, d165997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14871 q selected
    | true =>
      simp only [d164823, d165997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164824 q = 0) : d165998 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164824, d165998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164824, d165998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164893 q = 0) : d166067 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164893, d166067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164893, d166067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164894 q = 0) : d166068 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164894, d166068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164894, d166068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164895 q = 0) : d166069 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164895, d166069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164895, d166069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164896 q = 0) : d166070 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164896, d166070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164896, d166070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14888 (p : Pattern) (selected : d164900 p = 0) : d165971 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2201 q = 0) : d53314 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2201, d53314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro587 q selected
    | true =>
      simp only [d2201, d53314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2202 q = 0) : d53315 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2202, d53315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2202, d53315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10458 q = 0) : d101685 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10458, d101685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6772 q selected
    | true =>
      simp only [d10458, d101685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10460 q = 0) : d101687 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10460, d101687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10460, d101687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164898 q = 0) : d165969 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164898, d165969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164898, d165969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10468 q = 0) : d101674 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10468, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6773 q selected
    | true =>
      simp only [d10468, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10470 q = 0) : d101676 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10470, d101676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10470, d101676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10482 q = 0) : d101692 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10482, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6774 q selected
    | true =>
      simp only [d10482, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10484 q = 0) : d101694 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10484, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10484, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d164899 q = 0) : d165970 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164899, d165970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164899, d165970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164900 q = 0) : d165971 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164900, d165971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164900, d165971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14889 (p : Pattern) (selected : d164903 p = 0) : d165974 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2219 q = 0) : d53332 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2219, d53332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro592 q selected
    | true =>
      simp only [d2219, d53332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2220 q = 0) : d53333 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2220, d53333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2220, d53333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10493 q = 0) : d101712 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10493, d101712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6776 q selected
    | true =>
      simp only [d10493, d101712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10495 q = 0) : d101714 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10495, d101714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10495, d101714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164901 q = 0) : d165972 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164901, d165972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164901, d165972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10482 q = 0) : d101692 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10482, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6774 q selected
    | true =>
      simp only [d10482, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10484 q = 0) : d101694 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10484, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10484, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164902 q = 0) : d165973 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164902, d165973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164902, d165973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d164903 q = 0) : d165974 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164903, d165974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164903, d165974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro14890 (p : Pattern) (selected : d164909 p = 0) : d165980 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10508 q = 0) : d69331 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10508, d69331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6778 q selected
    | true =>
      simp only [d10508, d69331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10510 q = 0) : d69332 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10510, d69332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10510, d69332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164907 q = 0) : d165978 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164907, d165978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164907, d165978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10521 q = 0) : d101733 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10521, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6779 q selected
    | true =>
      simp only [d10521, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10523 q = 0) : d101735 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10523, d101735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10523, d101735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164908 q = 0) : d165979 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164908, d165979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164908, d165979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164909 q = 0) : d165980 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164909, d165980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164909, d165980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro14891 (p : Pattern) (selected : d164915 p = 0) : d165986 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2231 q = 0) : d53344 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2231, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro593 q selected
    | true =>
      simp only [d2231, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2232 q = 0) : d53345 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2232, d53345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2232, d53345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164914 q = 0) : d165985 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164914, d165985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164914, d165985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10521 q = 0) : d101733 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10521, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6779 q selected
    | true =>
      simp only [d10521, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10523 q = 0) : d101735 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10523, d101735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10523, d101735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164908 q = 0) : d165979 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164908, d165979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164908, d165979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164915 q = 0) : d165986 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164915, d165986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164915, d165986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro14892 (p : Pattern) (selected : d164921 p = 0) : d165992 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164904 q = 0) : d165975 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164904, d165975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14888 q selected
    | true =>
      simp only [d164904, d165975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14889 q selected
  have h2 (q : Pattern) (selected : d164905 q = 0) : d165976 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164905, d165976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164905, d165976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164906 q = 0) : d165977 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164906, d165977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164906, d165977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164910 q = 0) : d165981 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164910, d165981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14889 q selected
    | true =>
      simp only [d164910, d165981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14890 q selected
  have h5 (q : Pattern) (selected : d164911 q = 0) : d165982 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164911, d165982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164911, d165982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164912 q = 0) : d165983 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164912, d165983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164912, d165983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164913 q = 0) : d165984 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164913, d165984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164913, d165984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164916 q = 0) : d165987 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164916, d165987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14889 q selected
    | true =>
      simp only [d164916, d165987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14891 q selected
  have h9 (q : Pattern) (selected : d164917 q = 0) : d165988 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164917, d165988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164917, d165988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164918 q = 0) : d165989 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164918, d165989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164918, d165989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164919 q = 0) : d165990 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164919, d165990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164919, d165990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d164920 q = 0) : d165991 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164920, d165991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164920, d165991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d164921 q = 0) : d165992 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164921, d165992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d164921, d165992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro14893 (p : Pattern) (selected : d164925 p = 0) : d165996 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164916 q = 0) : d165987 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164916, d165987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14889 q selected
    | true =>
      simp only [d164916, d165987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14891 q selected
  have h2 (q : Pattern) (selected : d164917 q = 0) : d165988 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164917, d165988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164917, d165988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164918 q = 0) : d165989 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164918, d165989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164918, d165989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164919 q = 0) : d165990 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164919, d165990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164919, d165990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164924 q = 0) : d165995 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164924, d165995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164924, d165995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164925 q = 0) : d165996 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164925, d165996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164925, d165996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14894 (p : Pattern) (selected : d164931 p = 0) : d166002 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164922 q = 0) : d165993 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164922, d165993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14892 q selected
    | true =>
      simp only [d164922, d165993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164923 q = 0) : d165994 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164923, d165994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164923, d165994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164926 q = 0) : d165997 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164926, d165997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14893 q selected
    | true =>
      simp only [d164926, d165997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164927 q = 0) : d165998 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164927, d165998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164927, d165998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164928 q = 0) : d165999 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164928, d165999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164928, d165999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164929 q = 0) : d166000 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164929, d166000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164929, d166000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164930 q = 0) : d166001 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164930, d166001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164930, d166001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164931 q = 0) : d166002 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164931, d166002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164931, d166002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14895 (p : Pattern) (selected : d164935 p = 0) : d166006 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164926 q = 0) : d165997 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164926, d165997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14893 q selected
    | true =>
      simp only [d164926, d165997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164927 q = 0) : d165998 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164927, d165998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164927, d165998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164932 q = 0) : d166003 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164932, d166003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164932, d166003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164933 q = 0) : d166004 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164933, d166004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164933, d166004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164934 q = 0) : d166005 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164934, d166005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164934, d166005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164935 q = 0) : d166006 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164935, d166006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164935, d166006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14896 (p : Pattern) (selected : d164938 p = 0) : d166073 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2065 q = 0) : d53344 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro559 q selected
    | true =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2066 q = 0) : d53345 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164811 q = 0) : d165985 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164811, d165985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164811, d165985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164938 q = 0) : d166073 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164938, d166073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164938, d166073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro14897 (p : Pattern) (selected : d164944 p = 0) : d166079 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164801 q = 0) : d165975 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164801, d165975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14866 q selected
    | true =>
      simp only [d164801, d165975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14867 q selected
  have h2 (q : Pattern) (selected : d164802 q = 0) : d165976 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164802, d165976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164802, d165976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164803 q = 0) : d165977 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164803, d165977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164803, d165977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164807 q = 0) : d165981 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164807, d165981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14867 q selected
    | true =>
      simp only [d164807, d165981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14868 q selected
  have h5 (q : Pattern) (selected : d164808 q = 0) : d165982 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164808, d165982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164808, d165982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164809 q = 0) : d165983 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164809, d165983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164809, d165983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164810 q = 0) : d165984 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164810, d165984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164810, d165984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164939 q = 0) : d166074 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164939, d166074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14867 q selected
    | true =>
      simp only [d164939, d166074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14896 q selected
  have h9 (q : Pattern) (selected : d164940 q = 0) : d166075 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164940, d166075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164940, d166075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164941 q = 0) : d166076 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164941, d166076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164941, d166076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164942 q = 0) : d166077 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164942, d166077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164942, d166077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d164943 q = 0) : d166078 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164943, d166078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164943, d166078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d164944 q = 0) : d166079 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164944, d166079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d164944, d166079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro14898 (p : Pattern) (selected : d164950 p = 0) : d166085 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164945 q = 0) : d166080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164945, d166080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14897 q selected
    | true =>
      simp only [d164945, d166080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164946 q = 0) : d166081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164946, d166081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164946, d166081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164947 q = 0) : d166082 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164947, d166082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164947, d166082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164948 q = 0) : d166083 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164948, d166083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164948, d166083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164949 q = 0) : d166084 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164949, d166084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164949, d166084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164950 q = 0) : d166085 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164950, d166085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164950, d166085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14899 (p : Pattern) (selected : d164956 p = 0) : d166091 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164856 q = 0) : d166030 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164856, d166030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14878 q selected
    | true =>
      simp only [d164856, d166030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14879 q selected
  have h2 (q : Pattern) (selected : d164857 q = 0) : d166031 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164857, d166031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164857, d166031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164858 q = 0) : d166032 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164858, d166032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164858, d166032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164859 q = 0) : d166033 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164859, d166033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164859, d166033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164866 q = 0) : d166040 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164866, d166040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14880 q selected
    | true =>
      simp only [d164866, d166040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14881 q selected
  have h6 (q : Pattern) (selected : d164867 q = 0) : d166041 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164867, d166041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164867, d166041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164868 q = 0) : d166042 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164868, d166042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164868, d166042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164897 q = 0) : d166071 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164897, d166071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14886 q selected
    | true =>
      simp only [d164897, d166071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14887 q selected
  have h9 (q : Pattern) (selected : d164936 q = 0) : d166007 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164936, d166007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14894 q selected
    | true =>
      simp only [d164936, d166007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14895 q selected
  have h10 (q : Pattern) (selected : d164937 q = 0) : d166072 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164937, d166072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d164937, d166072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164951 q = 0) : d166086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164951, d166086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14898 q selected
    | true =>
      simp only [d164951, d166086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d164952 q = 0) : d166087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164952, d166087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d164952, d166087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d164953 q = 0) : d166088 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164953, d166088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164953, d166088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d164954 q = 0) : d166089 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164954, d166089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164954, d166089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d164955 q = 0) : d166090 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164955, d166090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164955, d166090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d164956 q = 0) : d166091 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164956, d166091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164956, d166091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro14900 (p : Pattern) (selected : d164957 p = 0) : d166092 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164819 q = 0) : d165993 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164819, d165993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14870 q selected
    | true =>
      simp only [d164819, d165993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164820 q = 0) : d165994 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164820, d165994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164820, d165994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164823 q = 0) : d165997 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164823, d165997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14871 q selected
    | true =>
      simp only [d164823, d165997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164824 q = 0) : d165998 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164824, d165998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164824, d165998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164825 q = 0) : d165999 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164825, d165999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164825, d165999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164826 q = 0) : d166000 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164826, d166000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164826, d166000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164852 q = 0) : d166026 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164852, d166026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164852, d166026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164957 q = 0) : d166092 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164957, d166092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164957, d166092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14901 (p : Pattern) (selected : d164958 p = 0) : d166093 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164823 q = 0) : d165997 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164823, d165997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14871 q selected
    | true =>
      simp only [d164823, d165997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164824 q = 0) : d165998 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164824, d165998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164824, d165998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164829 q = 0) : d166003 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164829, d166003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164829, d166003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164830 q = 0) : d166004 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164830, d166004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164830, d166004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164854 q = 0) : d166028 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164854, d166028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164854, d166028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164958 q = 0) : d166093 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164958, d166093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164958, d166093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14902 (p : Pattern) (selected : d164963 p = 0) : d166098 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164819 q = 0) : d165993 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164819, d165993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14870 q selected
    | true =>
      simp only [d164819, d165993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164820 q = 0) : d165994 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164820, d165994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164820, d165994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164823 q = 0) : d165997 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164823, d165997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14871 q selected
    | true =>
      simp only [d164823, d165997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164824 q = 0) : d165998 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164824, d165998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164824, d165998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164825 q = 0) : d165999 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164825, d165999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164825, d165999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164860 q = 0) : d166034 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164860, d166034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164860, d166034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164861 q = 0) : d166035 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164861, d166035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164861, d166035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164963 q = 0) : d166098 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164963, d166098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164963, d166098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14903 (p : Pattern) (selected : d164964 p = 0) : d166099 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164823 q = 0) : d165997 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164823, d165997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14871 q selected
    | true =>
      simp only [d164823, d165997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164824 q = 0) : d165998 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164824, d165998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164824, d165998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164829 q = 0) : d166003 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164829, d166003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164829, d166003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164863 q = 0) : d166037 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164863, d166037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164863, d166037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164864 q = 0) : d166038 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164864, d166038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164864, d166038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164964 q = 0) : d166099 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164964, d166099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164964, d166099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14904 (p : Pattern) (selected : d164968 p = 0) : d166103 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164882 q = 0) : d166056 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164882, d166056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14884 q selected
    | true =>
      simp only [d164882, d166056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164883 q = 0) : d166057 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164883, d166057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164883, d166057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164887 q = 0) : d166061 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164887, d166061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14885 q selected
    | true =>
      simp only [d164887, d166061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164888 q = 0) : d166062 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164888, d166062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164888, d166062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164889 q = 0) : d166063 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164889, d166063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164889, d166063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164890 q = 0) : d166064 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164890, d166064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164890, d166064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164891 q = 0) : d166065 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164891, d166065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164891, d166065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164968 q = 0) : d166103 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164968, d166103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164968, d166103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14905 (p : Pattern) (selected : d164969 p = 0) : d166104 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164887 q = 0) : d166061 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164887, d166061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14885 q selected
    | true =>
      simp only [d164887, d166061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164888 q = 0) : d166062 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164888, d166062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164888, d166062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164823 q = 0) : d165997 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164823, d165997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14871 q selected
    | true =>
      simp only [d164823, d165997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164824 q = 0) : d165998 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164824, d165998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164824, d165998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164893 q = 0) : d166067 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164893, d166067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164893, d166067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164894 q = 0) : d166068 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164894, d166068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164894, d166068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164895 q = 0) : d166069 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164895, d166069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164895, d166069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164969 q = 0) : d166104 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164969, d166104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164969, d166104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14906 (p : Pattern) (selected : d164971 p = 0) : d166015 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164922 q = 0) : d165993 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164922, d165993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14892 q selected
    | true =>
      simp only [d164922, d165993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164923 q = 0) : d165994 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164923, d165994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164923, d165994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164926 q = 0) : d165997 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164926, d165997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14893 q selected
    | true =>
      simp only [d164926, d165997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164927 q = 0) : d165998 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164927, d165998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164927, d165998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164928 q = 0) : d165999 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164928, d165999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164928, d165999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164929 q = 0) : d166000 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164929, d166000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164929, d166000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164930 q = 0) : d166001 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164930, d166001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164930, d166001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164971 q = 0) : d166015 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164971, d166015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164971, d166015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14907 (p : Pattern) (selected : d164972 p = 0) : d166016 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164926 q = 0) : d165997 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164926, d165997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14893 q selected
    | true =>
      simp only [d164926, d165997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164927 q = 0) : d165998 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164927, d165998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164927, d165998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164932 q = 0) : d166003 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164932, d166003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164932, d166003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164933 q = 0) : d166004 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164933, d166004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164933, d166004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164934 q = 0) : d166005 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164934, d166005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164934, d166005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164972 q = 0) : d166016 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164972, d166016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164972, d166016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14908 (p : Pattern) (selected : d164975 p = 0) : d166107 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164945 q = 0) : d166080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164945, d166080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14897 q selected
    | true =>
      simp only [d164945, d166080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164946 q = 0) : d166081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164946, d166081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164946, d166081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164947 q = 0) : d166082 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164947, d166082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164947, d166082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164948 q = 0) : d166083 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164948, d166083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164948, d166083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164949 q = 0) : d166084 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164949, d166084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164949, d166084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164975 q = 0) : d166107 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164975, d166107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164975, d166107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14909 (p : Pattern) (selected : d164981 p = 0) : d166113 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164856 q = 0) : d166030 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164856, d166030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14878 q selected
    | true =>
      simp only [d164856, d166030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14879 q selected
  have h2 (q : Pattern) (selected : d164857 q = 0) : d166031 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164857, d166031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164857, d166031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164858 q = 0) : d166032 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164858, d166032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164858, d166032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164859 q = 0) : d166033 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164859, d166033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164859, d166033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164866 q = 0) : d166040 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164866, d166040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14880 q selected
    | true =>
      simp only [d164866, d166040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14881 q selected
  have h6 (q : Pattern) (selected : d164867 q = 0) : d166041 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164867, d166041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164867, d166041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164868 q = 0) : d166042 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164868, d166042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164868, d166042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164897 q = 0) : d166071 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164897, d166071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14886 q selected
    | true =>
      simp only [d164897, d166071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14887 q selected
  have h9 (q : Pattern) (selected : d164936 q = 0) : d166007 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164936, d166007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14894 q selected
    | true =>
      simp only [d164936, d166007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14895 q selected
  have h10 (q : Pattern) (selected : d164937 q = 0) : d166072 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164937, d166072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d164937, d166072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164951 q = 0) : d166086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164951, d166086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14898 q selected
    | true =>
      simp only [d164951, d166086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d164952 q = 0) : d166087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164952, d166087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d164952, d166087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d164953 q = 0) : d166088 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164953, d166088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164953, d166088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d164954 q = 0) : d166089 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164954, d166089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164954, d166089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d164955 q = 0) : d166090 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164955, d166090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164955, d166090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d164959 q = 0) : d166094 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164959, d166094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14900 q selected
    | true =>
      simp only [d164959, d166094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14901 q selected
  have h17 (q : Pattern) (selected : d164960 q = 0) : d166095 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164960, d166095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164960, d166095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d164961 q = 0) : d166096 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164961, d166096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d164961, d166096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d164962 q = 0) : d166097 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164962, d166097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164962, d166097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d164965 q = 0) : d166100 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164965, d166100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14902 q selected
    | true =>
      simp only [d164965, d166100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14903 q selected
  have h21 (q : Pattern) (selected : d164966 q = 0) : d166101 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164966, d166101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164966, d166101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d164967 q = 0) : d166102 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164967, d166102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d164967, d166102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d164970 q = 0) : d166105 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164970, d166105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14904 q selected
    | true =>
      simp only [d164970, d166105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14905 q selected
  have h24 (q : Pattern) (selected : d164973 q = 0) : d166017 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164973, d166017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14906 q selected
    | true =>
      simp only [d164973, d166017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14907 q selected
  have h25 (q : Pattern) (selected : d164974 q = 0) : d166106 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164974, d166106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d164974, d166106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d164976 q = 0) : d166108 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164976, d166108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14908 q selected
    | true =>
      simp only [d164976, d166108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d164977 q = 0) : d166109 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164977, d166109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d164977, d166109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d164978 q = 0) : d166110 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164978, d166110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d164978, d166110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d164979 q = 0) : d166111 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164979, d166111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d164979, d166111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d164980 q = 0) : d166112 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164980, d166112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d164980, d166112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d164981 q = 0) : d166113 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164981, d166113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d164981, d166113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro14910 (p : Pattern) (selected : d164993 p = 0) : d166125 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164983 q = 0) : d166115 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164983, d166115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14887 q selected
    | true =>
      simp only [d164983, d166115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14873 q selected
  have h2 (q : Pattern) (selected : d164984 q = 0) : d166116 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164984, d166116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164984, d166116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164985 q = 0) : d166117 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164985, d166117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164985, d166117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164986 q = 0) : d166118 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164986, d166118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164986, d166118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164987 q = 0) : d166119 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164987, d166119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164987, d166119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164988 q = 0) : d166120 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164988, d166120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14873 q selected
    | true =>
      simp only [d164988, d166120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164989 q = 0) : d166121 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164989, d166121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164989, d166121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164990 q = 0) : d166122 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164990, d166122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164990, d166122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d164991 q = 0) : d166123 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164991, d166123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164991, d166123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164992 q = 0) : d166124 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164992, d166124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164992, d166124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164993 q = 0) : d166125 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164993, d166125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164993, d166125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14911 (p : Pattern) (selected : d164999 p = 0) : d166131 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164988 q = 0) : d166120 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164988, d166120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14873 q selected
    | true =>
      simp only [d164988, d166120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164989 q = 0) : d166121 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164989, d166121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164989, d166121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164990 q = 0) : d166122 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164990, d166122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164990, d166122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164991 q = 0) : d166123 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164991, d166123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164991, d166123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164992 q = 0) : d166124 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164992, d166124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164992, d166124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164994 q = 0) : d166126 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164994, d166126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14876 q selected
    | true =>
      simp only [d164994, d166126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164995 q = 0) : d166127 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164995, d166127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164995, d166127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164996 q = 0) : d166128 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164996, d166128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164996, d166128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d164997 q = 0) : d166129 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164997, d166129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164997, d166129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164998 q = 0) : d166130 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164998, d166130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164998, d166130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164999 q = 0) : d166131 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164999, d166131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164999, d166131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14912 (p : Pattern) (selected : d165006 p = 0) : d166138 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164970 q = 0) : d166105 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164970, d166105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14904 q selected
    | true =>
      simp only [d164970, d166105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14905 q selected
  have h2 (q : Pattern) (selected : d164973 q = 0) : d166017 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164973, d166017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14906 q selected
    | true =>
      simp only [d164973, d166017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14907 q selected
  have h3 (q : Pattern) (selected : d164974 q = 0) : d166106 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164974, d166106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164974, d166106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164976 q = 0) : d166108 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164976, d166108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14908 q selected
    | true =>
      simp only [d164976, d166108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164977 q = 0) : d166109 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164977, d166109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164977, d166109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164978 q = 0) : d166110 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164978, d166110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164978, d166110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d165004 q = 0) : d166136 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d165004, d166136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d165004, d166136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d165005 q = 0) : d166137 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d165005, d166137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d165005, d166137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d165006 q = 0) : d166138 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d165006, d166138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d165006, d166138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro14913 (p : Pattern) (selected : d165008 p = 0) : d166140 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164994 q = 0) : d166126 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164994, d166126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14876 q selected
    | true =>
      simp only [d164994, d166126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164995 q = 0) : d166127 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164995, d166127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164995, d166127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164996 q = 0) : d166128 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164996, d166128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164996, d166128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164997 q = 0) : d166129 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164997, d166129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164997, d166129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164998 q = 0) : d166130 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164998, d166130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164998, d166130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d165008 q = 0) : d166140 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d165008, d166140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d165008, d166140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14914 (p : Pattern) (selected : d165015 p = 0) : d166147 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d164839 q = 0) : d166013 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d164839, d166013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164839, d166013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14874 q selected
  have h2 (q : Pattern) (selected : d164840 q = 0) : d166014 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d164840, d166014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164840, d166014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164849 q = 0) : d166023 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d164849, d166023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14874 q selected
    | true =>
      simp only [d164849, d166023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14877 q selected
  have h4 (q : Pattern) (selected : d164850 q = 0) : d166024 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d164850, d166024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164850, d166024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164851 q = 0) : d166025 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d164851, d166025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164851, d166025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164982 q = 0) : d166114 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d164982, d166114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14899 q selected
    | true =>
      simp only [d164982, d166114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14909 q selected
  have h7 (q : Pattern) (selected : d165000 q = 0) : d166132 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d165000, d166132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14910 q selected
    | true =>
      simp only [d165000, d166132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14911 q selected
  have h8 (q : Pattern) (selected : d165001 q = 0) : d166133 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d165001, d166133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d165001, d166133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d165002 q = 0) : d166134 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d165002, d166134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d165002, d166134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d165003 q = 0) : d166135 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d165003, d166135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d165003, d166135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d165007 q = 0) : d166139 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d165007, d166139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d165007, d166139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14912 q selected
  have h12 (q : Pattern) (selected : d165009 q = 0) : d166141 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d165009, d166141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d165009, d166141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14913 q selected
  have h13 (q : Pattern) (selected : d165010 q = 0) : d166142 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d165010, d166142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d165010, d166142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d165011 q = 0) : d166143 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d165011, d166143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d165011, d166143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d165012 q = 0) : d166144 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d165012, d166144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d165012, d166144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d165013 q = 0) : d166145 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d165013, d166145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d165013, d166145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d165014 q = 0) : d166146 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d165014, d166146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d165014, d166146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d165015 q = 0) : d166147 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d165015, d166147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d165015, d166147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro14915 (p : Pattern) (selected : d165021 p = 0) : d166153 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d165016 q = 0) : d166148 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d165016, d166148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d165016, d166148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14914 q selected
  have h2 (q : Pattern) (selected : d165017 q = 0) : d166149 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d165017, d166149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d165017, d166149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d165018 q = 0) : d166150 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d165018, d166150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d165018, d166150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d165019 q = 0) : d166151 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d165019, d166151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d165019, d166151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d165020 q = 0) : d166152 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d165020, d166152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d165020, d166152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d165021 q = 0) : d166153 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d165021, d166153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d165021, d166153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14916 (p : Pattern) (selected : d165027 p = 0) : d166159 p = 1 := by
  have h0 (q : Pattern) (selected : d164141 q = 0) : d165434 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d164141, d165434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14684 q selected
    | true =>
      simp only [d164141, d165434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14722 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d164330 q = 0) : d165588 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d164330, d165588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164330, d165588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14765 q selected
  have h3 (q : Pattern) (selected : d164331 q = 0) : d165589 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d164331, d165589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164331, d165589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164560 q = 0) : d165776 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d164560, d165776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164560, d165776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14815 q selected
  have h5 (q : Pattern) (selected : d164561 q = 0) : d165777 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d164561, d165777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164561, d165777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164562 q = 0) : d165778 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d164562, d165778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164562, d165778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164791 q = 0) : d165965 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d164791, d165965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164791, d165965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14865 q selected
  have h8 (q : Pattern) (selected : d164792 q = 0) : d165966 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d164792, d165966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164792, d165966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d164793 q = 0) : d165967 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d164793, d165967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164793, d165967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164794 q = 0) : d165968 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d164794, d165968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164794, d165968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d165022 q = 0) : d166154 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d165022, d166154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d165022, d166154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14915 q selected
  have h12 (q : Pattern) (selected : d165023 q = 0) : d166155 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d165023, d166155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d165023, d166155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d165024 q = 0) : d166156 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d165024, d166156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d165024, d166156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d165025 q = 0) : d166157 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d165025, d166157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d165025, d166157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d165026 q = 0) : d166158 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d165026, d166158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d165026, d166158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d165027 q = 0) : d166159 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d165027, d166159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d165027, d166159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro14917 (p : Pattern) (selected : d165033 p = 0) : d166165 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d165028 q = 0) : d166160 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d165028, d166160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14916 q selected
    | true =>
      simp only [d165028, d166160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d165029 q = 0) : d166161 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d165029, d166161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d165029, d166161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d165030 q = 0) : d166162 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d165030, d166162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d165030, d166162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d165031 q = 0) : d166163 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d165031, d166163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d165031, d166163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d165032 q = 0) : d166164 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d165032, d166164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d165032, d166164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d165033 q = 0) : d166165 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d165033, d166165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d165033, d166165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14918 (p : Pattern) (selected : d165039 p = 0) : d166171 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d165034 q = 0) : d166166 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d165034, d166166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14917 q selected
    | true =>
      simp only [d165034, d166166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d165035 q = 0) : d166167 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d165035, d166167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d165035, d166167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d165036 q = 0) : d166168 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d165036, d166168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d165036, d166168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d165037 q = 0) : d166169 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d165037, d166169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d165037, d166169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d165038 q = 0) : d166170 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d165038, d166170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d165038, d166170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d165039 q = 0) : d166171 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d165039, d166171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d165039, d166171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14919 (p : Pattern) (selected : d165045 p = 0) : d166177 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d165040 q = 0) : d166172 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d165040, d166172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14918 q selected
    | true =>
      simp only [d165040, d166172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d165041 q = 0) : d166173 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d165041, d166173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d165041, d166173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d165042 q = 0) : d166174 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d165042, d166174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d165042, d166174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d165043 q = 0) : d166175 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d165043, d166175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d165043, d166175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d165044 q = 0) : d166176 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d165044, d166176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d165044, d166176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d165045 q = 0) : d166177 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d165045, d166177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d165045, d166177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14920 (p : Pattern) (selected : d165051 p = 0) : d166183 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d165046 q = 0) : d166178 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d165046, d166178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14919 q selected
    | true =>
      simp only [d165046, d166178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d165047 q = 0) : d166179 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d165047, d166179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d165047, d166179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d165048 q = 0) : d166180 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d165048, d166180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d165048, d166180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d165049 q = 0) : d166181 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d165049, d166181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d165049, d166181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d165050 q = 0) : d166182 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d165050, d166182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d165050, d166182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d165051 q = 0) : d166183 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d165051, d166183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d165051, d166183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14921 (p : Pattern) (selected : d165057 p = 0) : d166189 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d165052 q = 0) : d166184 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d165052, d166184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14920 q selected
    | true =>
      simp only [d165052, d166184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d165053 q = 0) : d166185 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d165053, d166185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d165053, d166185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d165054 q = 0) : d166186 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d165054, d166186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d165054, d166186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d165055 q = 0) : d166187 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d165055, d166187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d165055, d166187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d165056 q = 0) : d166188 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d165056, d166188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d165056, d166188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d165057 q = 0) : d166189 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d165057, d166189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d165057, d166189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14922 (p : Pattern) (selected : d165063 p = 0) : d166195 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d165058 q = 0) : d166190 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d165058, d166190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14921 q selected
    | true =>
      simp only [d165058, d166190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d165059 q = 0) : d166191 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d165059, d166191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d165059, d166191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d165060 q = 0) : d166192 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d165060, d166192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d165060, d166192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d165061 q = 0) : d166193 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d165061, d166193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d165061, d166193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d165062 q = 0) : d166194 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d165062, d166194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d165062, d166194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d165063 q = 0) : d166195 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d165063, d166195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d165063, d166195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14923 (p : Pattern) (selected : d165069 p = 0) : d166201 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d165064 q = 0) : d166196 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d165064, d166196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14922 q selected
    | true =>
      simp only [d165064, d166196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d165065 q = 0) : d166197 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d165065, d166197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d165065, d166197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d165066 q = 0) : d166198 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d165066, d166198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d165066, d166198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d165067 q = 0) : d166199 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d165067, d166199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d165067, d166199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d165068 q = 0) : d166200 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d165068, d166200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d165068, d166200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d165069 q = 0) : d166201 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d165069, d166201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d165069, d166201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14924 (p : Pattern) (selected : d163801 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d170 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
    | true =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d171 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d163800 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d163800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163801 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d163801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d163801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro14925 (p : Pattern) (selected : d163807 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d163802 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d163802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14924 q selected
    | true =>
      simp only [d163802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163803 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d163803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163804 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d163804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d163805 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d163805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d163805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d163806 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d163806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d163806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d163807 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d163807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14926 (p : Pattern) (selected : d163813 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d163808 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14925 q selected
    | true =>
      simp only [d163808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163809 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163810 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163811 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d163811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d163812 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d163812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d163813 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14927 (p : Pattern) (selected : d163819 p = 1) : d166206 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d163778 q = 1) : d163778 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d163784 q = 1) : d163784 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d163799 q = 1) : d163799 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d163814 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14926 q selected
    | true =>
      simp only [d163814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d163815 q = 1) : d166202 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163815, d166202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d163815, d166202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163730 q = 1) : d163730 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d163816 q = 1) : d166203 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163816, d166203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163816, d166203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d163817 q = 1) : d166204 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163817, d166204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163817, d166204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d163818 q = 1) : d166205 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163818, d166205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d163818, d166205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d163819 q = 1) : d166206 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163819, d166206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163819, d166206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro14928 (p : Pattern) (selected : d163831 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d163808 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14925 q selected
    | true =>
      simp only [d163808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163809 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163810 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163811 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d163811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d163812 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d163812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d163831 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14929 (p : Pattern) (selected : d163837 p = 1) : d166211 p = 1 := by
  have h0 (q : Pattern) (selected : d163778 q = 1) : d163778 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d163784 q = 1) : d163784 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d163799 q = 1) : d163799 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d163814 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14926 q selected
    | true =>
      simp only [d163814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163815 q = 1) : d166202 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163815, d166202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163815, d166202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163730 q = 1) : d163730 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d163816 q = 1) : d166203 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163816, d166203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163816, d166203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d163817 q = 1) : d166204 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163817, d166204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d163817, d166204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d163818 q = 1) : d166205 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163818, d166205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163818, d166205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d163824 q = 1) : d163824 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d163828 q = 1) : d163828 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d163830 q = 1) : d163830 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d163832 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14928 q selected
    | true =>
      simp only [d163832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d163833 q = 1) : d166207 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163833, d166207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d163833, d166207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d163737 q = 1) : d163737 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d163834 q = 1) : d166208 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163834, d166208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d163834, d166208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d163835 q = 1) : d166209 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163835, d166209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d163835, d166209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d163836 q = 1) : d166210 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163836, d166210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d163836, d166210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d163837 q = 1) : d166211 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163837, d166211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d163837, d166211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro14930 (p : Pattern) (selected : d163846 p = 1) : d166218 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d163830 q = 1) : d163830 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d163832 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14928 q selected
    | true =>
      simp only [d163832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d163833 q = 1) : d166207 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163833, d166207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d163833, d166207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d163737 q = 1) : d163737 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d163834 q = 1) : d166208 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163834, d166208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d163834, d166208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163844 q = 1) : d166216 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163844, d166216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163844, d166216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d163845 q = 1) : d166217 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163845, d166217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163845, d166217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d163846 q = 1) : d166218 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163846, d166218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163846, d166218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14931 (p : Pattern) (selected : d163853 p = 1) : d166225 p = 1 := by
  have h0 (q : Pattern) (selected : d163772 q = 1) : d163772 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d163838 q = 1) : d166212 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163838, d166212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14927 q selected
    | true =>
      simp only [d163838, d166212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14929 q selected
  have h2 (q : Pattern) (selected : d163840 q = 1) : d163840 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d163841 q = 1) : d166213 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163841, d166213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d163841, d166213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d163842 q = 1) : d166214 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163842, d166214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d163842, d166214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163843 q = 1) : d166215 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163843, d166215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163843, d166215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d163847 q = 1) : d166219 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163847, d166219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d163847, d166219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14930 q selected
  have h8 (q : Pattern) (selected : d163848 q = 1) : d166220 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163848, d166220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d163848, d166220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d163849 q = 1) : d166221 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163849, d166221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d163849, d166221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d163850 q = 1) : d166222 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163850, d166222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d163850, d166222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d163851 q = 1) : d166223 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163851, d166223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d163851, d166223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d163852 q = 1) : d166224 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163852, d166224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d163852, d166224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h13 (q : Pattern) (selected : d163853 q = 1) : d166225 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d163853, d166225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d163853, d166225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro14932 (p : Pattern) (selected : d163903 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d350 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15 q selected
    | true =>
      simp only [d350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d351 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d170 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
    | true =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d171 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d163902 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d163902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163800 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d163800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d163800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d163903 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d163903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro14933 (p : Pattern) (selected : d163909 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d163904 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d163904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14932 q selected
    | true =>
      simp only [d163904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14924 q selected
  have h2 (q : Pattern) (selected : d163905 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d163905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163906 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d163906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d163802 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d163802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14924 q selected
    | true =>
      simp only [d163802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d163803 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d163803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163804 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d163804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d163907 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d163907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d163907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d163805 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d163805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d163805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d163908 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d163908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d163908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d163909 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d163909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d163909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro14934 (p : Pattern) (selected : d163915 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d163910 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14933 q selected
    | true =>
      simp only [d163910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163911 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163808 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14925 q selected
    | true =>
      simp only [d163808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163809 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163912 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163913 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d163914 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d163914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d163915 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14935 (p : Pattern) (selected : d163927 p = 1) : d166235 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d163879 q = 1) : d163879 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d163885 q = 1) : d163885 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d163901 q = 1) : d163901 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d163916 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14934 q selected
    | true =>
      simp only [d163916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14926 q selected
  have h5 (q : Pattern) (selected : d163917 q = 1) : d166231 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163917, d166231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d163917, d166231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163923 q = 1) : d163923 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d163924 q = 1) : d166232 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163924, d166232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163924, d166232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d163925 q = 1) : d166233 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163925, d166233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163925, d166233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d163926 q = 1) : d166234 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163926, d166234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d163926, d166234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d163927 q = 1) : d166235 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163927, d166235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163927, d166235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro14936 (p : Pattern) (selected : d163939 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d163910 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14933 q selected
    | true =>
      simp only [d163910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d163911 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163808 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14925 q selected
    | true =>
      simp only [d163808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d163809 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163912 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163913 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d163913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d163914 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d163914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d163939 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d163939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14937 (p : Pattern) (selected : d163948 p = 1) : d166240 p = 1 := by
  have h0 (q : Pattern) (selected : d163879 q = 1) : d163879 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d163885 q = 1) : d163885 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d163901 q = 1) : d163901 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d163916 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14934 q selected
    | true =>
      simp only [d163916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14926 q selected
  have h4 (q : Pattern) (selected : d163917 q = 1) : d166231 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163917, d166231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d163917, d166231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163923 q = 1) : d163923 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d163924 q = 1) : d166232 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163924, d166232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d163924, d166232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d163925 q = 1) : d166233 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163925, d166233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d163925, d166233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d163926 q = 1) : d166234 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163926, d166234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163926, d166234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d163932 q = 1) : d163932 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d163936 q = 1) : d163936 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d163938 q = 1) : d163938 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d163940 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14936 q selected
    | true =>
      simp only [d163940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14928 q selected
  have h13 (q : Pattern) (selected : d163941 q = 1) : d166236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163941, d166236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d163941, d166236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d163944 q = 1) : d163944 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d163945 q = 1) : d166237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163945, d166237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d163945, d166237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d163946 q = 1) : d166238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163946, d166238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d163946, d166238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d163947 q = 1) : d166239 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163947, d166239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d163947, d166239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d163948 q = 1) : d166240 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163948, d166240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d163948, d166240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro14938 (p : Pattern) (selected : d163957 p = 1) : d166247 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d163938 q = 1) : d163938 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d163940 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14936 q selected
    | true =>
      simp only [d163940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14928 q selected
  have h3 (q : Pattern) (selected : d163941 q = 1) : d166236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163941, d166236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d163941, d166236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d163944 q = 1) : d163944 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d163945 q = 1) : d166237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163945, d166237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d163945, d166237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163955 q = 1) : d166245 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163955, d166245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163955, d166245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d163956 q = 1) : d166246 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163956, d166246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163956, d166246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d163957 q = 1) : d166247 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163957, d166247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163957, d166247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14939 (p : Pattern) (selected : d163966 p = 1) : d166254 p = 1 := by
  have h0 (q : Pattern) (selected : d163873 q = 1) : d163873 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d163949 q = 1) : d166241 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163949, d166241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14935 q selected
    | true =>
      simp only [d163949, d166241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14937 q selected
  have h2 (q : Pattern) (selected : d163951 q = 1) : d163951 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d163952 q = 1) : d166242 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163952, d166242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d163952, d166242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d163953 q = 1) : d166243 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163953, d166243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d163953, d166243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163954 q = 1) : d166244 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163954, d166244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163954, d166244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d163958 q = 1) : d166248 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163958, d166248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d163958, d166248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14938 q selected
  have h8 (q : Pattern) (selected : d163960 q = 1) : d163960 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d163961 q = 1) : d166249 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163961, d166249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d163961, d166249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d163962 q = 1) : d166250 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163962, d166250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d163962, d166250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d163963 q = 1) : d166251 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163963, d166251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d163963, d166251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d163964 q = 1) : d166252 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163964, d166252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d163964, d166252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d163965 q = 1) : d166253 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163965, d166253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d163965, d166253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d163966 q = 1) : d166254 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d163966, d166254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d163966, d166254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro14940 (p : Pattern) (selected : d163972 p = 1) : d166260 p = 1 := by
  have h0 (q : Pattern) (selected : d163757 q = 1) : d163757 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d163854 q = 1) : d166226 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d163854, d166226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d163854, d166226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14931 q selected
  have h3 (q : Pattern) (selected : d163855 q = 1) : d166227 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d163855, d166227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d163855, d166227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d163856 q = 1) : d166228 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d163856, d166228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d163856, d166228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d163857 q = 1) : d166229 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d163857, d166229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d163857, d166229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163858 q = 1) : d166230 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d163858, d166230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163858, d166230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d163967 q = 1) : d166255 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d163967, d166255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d163967, d166255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14939 q selected
  have h8 (q : Pattern) (selected : d163968 q = 1) : d166256 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d163968, d166256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d163968, d166256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d163969 q = 1) : d166257 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d163969, d166257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d163969, d166257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d163970 q = 1) : d166258 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d163970, d166258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d163970, d166258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d163971 q = 1) : d166259 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d163971, d166259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d163971, d166259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d163972 q = 1) : d166260 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d163972, d166260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d163972, d166260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro14941 (p : Pattern) (selected : d164048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d574 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30 q selected
    | true =>
      simp only [d574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d575 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d350 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15 q selected
    | true =>
      simp only [d350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164046 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9512 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6813 q selected
    | true =>
      simp only [d9512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9514 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d170 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
    | true =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d171 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d164047 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164048 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14942 (p : Pattern) (selected : d164055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164049 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14941 q selected
    | true =>
      simp only [d164049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14932 q selected
  have h2 (q : Pattern) (selected : d164050 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164051 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d163904 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d163904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14932 q selected
    | true =>
      simp only [d163904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14924 q selected
  have h5 (q : Pattern) (selected : d163905 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d163905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d163906 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d163906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164052 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164053 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d164054 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164055 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d164055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro14943 (p : Pattern) (selected : d164059 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d163904 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d163904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14932 q selected
    | true =>
      simp only [d163904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14924 q selected
  have h2 (q : Pattern) (selected : d163905 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d163905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d163906 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d163906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d163906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164053 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164058 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164059 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14944 (p : Pattern) (selected : d164065 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164056 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14942 q selected
    | true =>
      simp only [d164056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164057 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164060 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14943 q selected
    | true =>
      simp only [d164060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164061 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164062 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164063 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164064 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164065 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14945 (p : Pattern) (selected : d164069 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164060 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14943 q selected
    | true =>
      simp only [d164060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164061 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164066 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164067 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164068 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164069 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14946 (p : Pattern) (selected : d164081 p = 1) : d166265 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164016 q = 1) : d164016 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d164025 q = 1) : d164025 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d164045 q = 1) : d164045 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d164070 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14944 q selected
    | true =>
      simp only [d164070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14945 q selected
  have h5 (q : Pattern) (selected : d164071 q = 1) : d166261 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164071, d166261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164071, d166261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164077 q = 1) : d164077 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d164078 q = 1) : d166262 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164078, d166262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164078, d166262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164079 q = 1) : d166263 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164079, d166263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164079, d166263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d164080 q = 1) : d166264 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164080, d166264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164080, d166264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164081 q = 1) : d166265 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164081, d166265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164081, d166265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro14947 (p : Pattern) (selected : d164095 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164056 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14942 q selected
    | true =>
      simp only [d164056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164057 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164060 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14943 q selected
    | true =>
      simp only [d164060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164061 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164062 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164063 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164064 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164095 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14948 (p : Pattern) (selected : d164096 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164060 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14943 q selected
    | true =>
      simp only [d164060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164061 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164066 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164067 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164068 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164096 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14949 (p : Pattern) (selected : d164105 p = 1) : d166270 p = 1 := by
  have h0 (q : Pattern) (selected : d164016 q = 1) : d164016 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164025 q = 1) : d164025 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d164045 q = 1) : d164045 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d164070 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14944 q selected
    | true =>
      simp only [d164070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14945 q selected
  have h4 (q : Pattern) (selected : d164071 q = 1) : d166261 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164071, d166261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164071, d166261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164077 q = 1) : d164077 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d164078 q = 1) : d166262 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164078, d166262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164078, d166262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164079 q = 1) : d166263 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164079, d166263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164079, d166263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164080 q = 1) : d166264 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164080, d166264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164080, d166264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d164087 q = 1) : d164087 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d164092 q = 1) : d164092 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d164094 q = 1) : d164094 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d164097 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14947 q selected
    | true =>
      simp only [d164097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14948 q selected
  have h13 (q : Pattern) (selected : d164098 q = 1) : d166266 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164098, d166266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d164098, d166266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d164101 q = 1) : d164101 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d164102 q = 1) : d166267 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164102, d166267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d164102, d166267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d164103 q = 1) : d166268 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164103, d166268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164103, d166268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d164104 q = 1) : d166269 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164104, d166269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d164104, d166269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d164105 q = 1) : d166270 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164105, d166270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d164105, d166270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro14950 (p : Pattern) (selected : d164125 p = 1) : d166277 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164094 q = 1) : d164094 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d164097 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14947 q selected
    | true =>
      simp only [d164097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14948 q selected
  have h3 (q : Pattern) (selected : d164098 q = 1) : d166266 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164098, d166266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164098, d166266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164101 q = 1) : d164101 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d164102 q = 1) : d166267 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164102, d166267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164102, d166267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164123 q = 1) : d166275 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164123, d166275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164123, d166275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164124 q = 1) : d166276 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164124, d166276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164124, d166276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164125 q = 1) : d166277 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164125, d166277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164125, d166277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14951 (p : Pattern) (selected : d164134 p = 1) : d166284 p = 1 := by
  have h0 (q : Pattern) (selected : d164008 q = 1) : d164008 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164106 q = 1) : d166271 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d164106, d166271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14946 q selected
    | true =>
      simp only [d164106, d166271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14949 q selected
  have h2 (q : Pattern) (selected : d164119 q = 1) : d164119 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d164120 q = 1) : d166272 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d164120, d166272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164120, d166272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d164121 q = 1) : d166273 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d164121, d166273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164121, d166273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164122 q = 1) : d166274 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d164122, d166274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164122, d166274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164126 q = 1) : d166278 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d164126, d166278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164126, d166278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14950 q selected
  have h8 (q : Pattern) (selected : d164128 q = 1) : d164128 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d164129 q = 1) : d166279 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d164129, d166279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164129, d166279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164130 q = 1) : d166280 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d164130, d166280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d164130, d166280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d164131 q = 1) : d166281 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d164131, d166281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164131, d166281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d164132 q = 1) : d166282 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d164132, d166282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164132, d166282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d164133 q = 1) : d166283 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d164133, d166283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d164133, d166283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d164134 q = 1) : d166284 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d164134, d166284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d164134, d166284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro14952 (p : Pattern) (selected : d164140 p = 1) : d166290 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164135 q = 1) : d166285 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d164135, d166285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164135, d166285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14951 q selected
  have h2 (q : Pattern) (selected : d164136 q = 1) : d166286 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d164136, d166286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164136, d166286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164137 q = 1) : d166287 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d164137, d166287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164137, d166287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164138 q = 1) : d166288 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d164138, d166288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164138, d166288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164139 q = 1) : d166289 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d164139, d166289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164139, d166289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164140 q = 1) : d166290 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d164140, d166290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164140, d166290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14953 (p : Pattern) (selected : d164230 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d868 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro51 q selected
    | true =>
      simp only [d868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d869 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d9661 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6823 q selected
    | true =>
      simp only [d9661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9663 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164228 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9671 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6824 q selected
    | true =>
      simp only [d9671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9673 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d874 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro52 q selected
    | true =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d875 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d164229 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164230 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14954 (p : Pattern) (selected : d164233 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d574 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30 q selected
    | true =>
      simp only [d574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d575 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d874 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro52 q selected
    | true =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d875 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164231 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164232 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164233 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro14955 (p : Pattern) (selected : d164237 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d874 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro52 q selected
    | true =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d875 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164232 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164237 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro14956 (p : Pattern) (selected : d164244 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164234 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14953 q selected
    | true =>
      simp only [d164234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14954 q selected
  have h2 (q : Pattern) (selected : d164235 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164236 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164238 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14954 q selected
    | true =>
      simp only [d164238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14955 q selected
  have h5 (q : Pattern) (selected : d164239 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164240 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164241 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164242 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d164243 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164244 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d164244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro14957 (p : Pattern) (selected : d164248 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164238 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14954 q selected
    | true =>
      simp only [d164238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14955 q selected
  have h2 (q : Pattern) (selected : d164239 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164240 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164242 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164247 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164248 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14958 (p : Pattern) (selected : d164254 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164245 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14956 q selected
    | true =>
      simp only [d164245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164246 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164249 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14957 q selected
    | true =>
      simp only [d164249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164250 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164251 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164252 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164253 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164254 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14959 (p : Pattern) (selected : d164258 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164249 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14957 q selected
    | true =>
      simp only [d164249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164250 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164255 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164256 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164257 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164258 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14960 (p : Pattern) (selected : d164270 p = 1) : d166296 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164198 q = 1) : d164198 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d164207 q = 1) : d164207 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d164227 q = 1) : d164227 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d164259 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14958 q selected
    | true =>
      simp only [d164259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14959 q selected
  have h5 (q : Pattern) (selected : d164260 q = 1) : d166292 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164260, d166292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164260, d166292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164266 q = 1) : d164266 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d164267 q = 1) : d166293 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164267, d166293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164267, d166293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164268 q = 1) : d166294 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164268, d166294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164268, d166294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d164269 q = 1) : d166295 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164269, d166295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164269, d166295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164270 q = 1) : d166296 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164270, d166296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164270, d166296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro14961 (p : Pattern) (selected : d164284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164245 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14956 q selected
    | true =>
      simp only [d164245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164246 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164249 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14957 q selected
    | true =>
      simp only [d164249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164250 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164251 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164252 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164253 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164284 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14962 (p : Pattern) (selected : d164285 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164249 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14957 q selected
    | true =>
      simp only [d164249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164250 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164255 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164256 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164257 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164285 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14963 (p : Pattern) (selected : d164294 p = 1) : d166301 p = 1 := by
  have h0 (q : Pattern) (selected : d164198 q = 1) : d164198 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164207 q = 1) : d164207 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d164227 q = 1) : d164227 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d164259 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14958 q selected
    | true =>
      simp only [d164259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14959 q selected
  have h4 (q : Pattern) (selected : d164260 q = 1) : d166292 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164260, d166292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164260, d166292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164266 q = 1) : d164266 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d164267 q = 1) : d166293 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164267, d166293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164267, d166293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164268 q = 1) : d166294 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164268, d166294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164268, d166294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164269 q = 1) : d166295 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164269, d166295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164269, d166295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d164276 q = 1) : d164276 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d164281 q = 1) : d164281 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d164283 q = 1) : d164283 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d164286 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14961 q selected
    | true =>
      simp only [d164286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14962 q selected
  have h13 (q : Pattern) (selected : d164287 q = 1) : d166297 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164287, d166297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d164287, d166297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d164290 q = 1) : d164290 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d164291 q = 1) : d166298 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164291, d166298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d164291, d166298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d164292 q = 1) : d166299 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164292, d166299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164292, d166299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d164293 q = 1) : d166300 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164293, d166300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d164293, d166300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d164294 q = 1) : d166301 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164294, d166301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d164294, d166301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro14964 (p : Pattern) (selected : d164314 p = 1) : d166308 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164283 q = 1) : d164283 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d164286 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14961 q selected
    | true =>
      simp only [d164286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14962 q selected
  have h3 (q : Pattern) (selected : d164287 q = 1) : d166297 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164287, d166297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164287, d166297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164290 q = 1) : d164290 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d164291 q = 1) : d166298 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164291, d166298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164291, d166298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164312 q = 1) : d166306 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164312, d166306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164312, d166306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164313 q = 1) : d166307 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164313, d166307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164313, d166307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164314 q = 1) : d166308 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164314, d166308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164314, d166308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14965 (p : Pattern) (selected : d164323 p = 1) : d166315 p = 1 := by
  have h0 (q : Pattern) (selected : d164190 q = 1) : d164190 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164295 q = 1) : d166302 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d164295, d166302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14960 q selected
    | true =>
      simp only [d164295, d166302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14963 q selected
  have h2 (q : Pattern) (selected : d164308 q = 1) : d164308 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d164309 q = 1) : d166303 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d164309, d166303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164309, d166303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d164310 q = 1) : d166304 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d164310, d166304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164310, d166304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164311 q = 1) : d166305 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d164311, d166305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164311, d166305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164315 q = 1) : d166309 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d164315, d166309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164315, d166309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14964 q selected
  have h8 (q : Pattern) (selected : d164317 q = 1) : d164317 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d164318 q = 1) : d166310 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d164318, d166310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164318, d166310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164319 q = 1) : d166311 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d164319, d166311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d164319, d166311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d164320 q = 1) : d166312 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d164320, d166312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164320, d166312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d164321 q = 1) : d166313 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d164321, d166313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164321, d166313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d164322 q = 1) : d166314 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d164322, d166314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d164322, d166314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d164323 q = 1) : d166315 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d164323, d166315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d164323, d166315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro14966 (p : Pattern) (selected : d164329 p = 1) : d166321 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164324 q = 1) : d166316 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d164324, d166316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164324, d166316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14965 q selected
  have h2 (q : Pattern) (selected : d164325 q = 1) : d166317 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d164325, d166317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164325, d166317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164326 q = 1) : d166318 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d164326, d166318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164326, d166318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164327 q = 1) : d166319 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d164327, d166319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164327, d166319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164328 q = 1) : d166320 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d164328, d166320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164328, d166320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164329 q = 1) : d166321 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d164329, d166321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164329, d166321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14967 (p : Pattern) (selected : d164438 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1255 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro79 q selected
    | true =>
      simp only [d1255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1256 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d9896 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6837 q selected
    | true =>
      simp only [d9896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9898 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164436 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9908 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6838 q selected
    | true =>
      simp only [d9908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9910 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6839 q selected
    | true =>
      simp only [d9918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d9920 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d164437 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164438 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14968 (p : Pattern) (selected : d164441 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1265 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro80 q selected
    | true =>
      simp only [d1265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1266 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1276 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro81 q selected
    | true =>
      simp only [d1276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1277 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164439 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6839 q selected
    | true =>
      simp only [d9918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9920 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164440 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d164441 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro14969 (p : Pattern) (selected : d164447 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d9943 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6842 q selected
    | true =>
      simp only [d9943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9945 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164445 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9952 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6843 q selected
    | true =>
      simp only [d9952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9954 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164446 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164447 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro14970 (p : Pattern) (selected : d164453 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1276 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro81 q selected
    | true =>
      simp only [d1276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1277 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164452 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9952 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6843 q selected
    | true =>
      simp only [d9952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9954 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164446 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164453 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro14971 (p : Pattern) (selected : d164459 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164442 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14967 q selected
    | true =>
      simp only [d164442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14968 q selected
  have h2 (q : Pattern) (selected : d164443 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164444 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164448 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14968 q selected
    | true =>
      simp only [d164448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14969 q selected
  have h5 (q : Pattern) (selected : d164449 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164450 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164451 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164454 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14968 q selected
    | true =>
      simp only [d164454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14970 q selected
  have h9 (q : Pattern) (selected : d164455 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164456 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164457 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d164458 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d164459 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d164459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro14972 (p : Pattern) (selected : d164463 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164454 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14968 q selected
    | true =>
      simp only [d164454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14970 q selected
  have h2 (q : Pattern) (selected : d164455 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164456 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164457 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164462 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164463 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14973 (p : Pattern) (selected : d164469 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164460 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14971 q selected
    | true =>
      simp only [d164460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164461 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164464 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14972 q selected
    | true =>
      simp only [d164464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164465 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164466 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164467 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164468 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164469 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14974 (p : Pattern) (selected : d164473 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164464 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14972 q selected
    | true =>
      simp only [d164464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164465 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164470 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164473 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14975 (p : Pattern) (selected : d164494 p = 1) : d166328 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164396 q = 1) : d164396 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d164405 q = 1) : d164405 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d164435 q = 1) : d164435 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d164474 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14973 q selected
    | true =>
      simp only [d164474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14974 q selected
  have h5 (q : Pattern) (selected : d164475 q = 1) : d166324 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164475, d166324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164475, d166324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164490 q = 1) : d164490 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d164491 q = 1) : d166325 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164491, d166325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164491, d166325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164492 q = 1) : d166326 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164492, d166326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164492, d166326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d164493 q = 1) : d166327 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164493, d166327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164493, d166327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164494 q = 1) : d166328 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164494, d166328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164494, d166328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro14976 (p : Pattern) (selected : d164509 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164460 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14971 q selected
    | true =>
      simp only [d164460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164461 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164464 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14972 q selected
    | true =>
      simp only [d164464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164465 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164466 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164467 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164468 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164509 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14977 (p : Pattern) (selected : d164510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164464 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14972 q selected
    | true =>
      simp only [d164464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164465 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164470 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164471 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164510 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14978 (p : Pattern) (selected : d164519 p = 1) : d166333 p = 1 := by
  have h0 (q : Pattern) (selected : d164396 q = 1) : d164396 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164405 q = 1) : d164405 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d164435 q = 1) : d164435 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d164474 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14973 q selected
    | true =>
      simp only [d164474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14974 q selected
  have h4 (q : Pattern) (selected : d164475 q = 1) : d166324 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164475, d166324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164475, d166324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164490 q = 1) : d164490 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d164491 q = 1) : d166325 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164491, d166325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164491, d166325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164492 q = 1) : d166326 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164492, d166326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164492, d166326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164493 q = 1) : d166327 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164493, d166327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164493, d166327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d164500 q = 1) : d164500 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d164505 q = 1) : d164505 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d164508 q = 1) : d164508 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d164511 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14976 q selected
    | true =>
      simp only [d164511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14977 q selected
  have h13 (q : Pattern) (selected : d164512 q = 1) : d166329 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164512, d166329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d164512, d166329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d164515 q = 1) : d164515 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d164516 q = 1) : d166330 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164516, d166330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d164516, d166330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d164517 q = 1) : d166331 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164517, d166331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164517, d166331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d164518 q = 1) : d166332 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164518, d166332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d164518, d166332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d164519 q = 1) : d166333 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164519, d166333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d164519, d166333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro14979 (p : Pattern) (selected : d164544 p = 1) : d166340 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164508 q = 1) : d164508 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d164511 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14976 q selected
    | true =>
      simp only [d164511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14977 q selected
  have h3 (q : Pattern) (selected : d164512 q = 1) : d166329 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164512, d166329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164512, d166329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164515 q = 1) : d164515 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d164516 q = 1) : d166330 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164516, d166330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164516, d166330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164542 q = 1) : d166338 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164542, d166338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164542, d166338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164543 q = 1) : d166339 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164543, d166339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164543, d166339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164544 q = 1) : d166340 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164544, d166340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164544, d166340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14980 (p : Pattern) (selected : d164553 p = 1) : d166347 p = 1 := by
  have h0 (q : Pattern) (selected : d164388 q = 1) : d164388 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164520 q = 1) : d166334 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d164520, d166334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14975 q selected
    | true =>
      simp only [d164520, d166334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14978 q selected
  have h2 (q : Pattern) (selected : d164538 q = 1) : d164538 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d164539 q = 1) : d166335 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d164539, d166335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164539, d166335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d164540 q = 1) : d166336 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d164540, d166336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164540, d166336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164541 q = 1) : d166337 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d164541, d166337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164541, d166337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164545 q = 1) : d166341 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d164545, d166341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164545, d166341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14979 q selected
  have h8 (q : Pattern) (selected : d164547 q = 1) : d164547 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d164548 q = 1) : d166342 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d164548, d166342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164548, d166342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164549 q = 1) : d166343 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d164549, d166343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d164549, d166343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d164550 q = 1) : d166344 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d164550, d166344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164550, d166344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d164551 q = 1) : d166345 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d164551, d166345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164551, d166345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d164552 q = 1) : d166346 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d164552, d166346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d164552, d166346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d164553 q = 1) : d166347 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d164553, d166347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d164553, d166347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro14981 (p : Pattern) (selected : d164559 p = 1) : d166353 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164554 q = 1) : d166348 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d164554, d166348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164554, d166348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14980 q selected
  have h2 (q : Pattern) (selected : d164555 q = 1) : d166349 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d164555, d166349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164555, d166349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164556 q = 1) : d166350 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d164556, d166350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164556, d166350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164557 q = 1) : d166351 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d164557, d166351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164557, d166351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164558 q = 1) : d166352 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d164558, d166352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164558, d166352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164559 q = 1) : d166353 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d164559, d166353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164559, d166353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14982 (p : Pattern) (selected : d164669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1726 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro113 q selected
    | true =>
      simp only [d1726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1727 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10190 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6855 q selected
    | true =>
      simp only [d10190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10192 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164667 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10200 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6856 q selected
    | true =>
      simp only [d10200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10202 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10215 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6857 q selected
    | true =>
      simp only [d10215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10217 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d164668 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164669 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14983 (p : Pattern) (selected : d164672 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1741 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro116 q selected
    | true =>
      simp only [d1741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1742 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10226 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6859 q selected
    | true =>
      simp only [d10226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10228 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164670 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10215 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6857 q selected
    | true =>
      simp only [d10215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10217 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164671 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d164672 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro14984 (p : Pattern) (selected : d164678 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10243 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6861 q selected
    | true =>
      simp only [d10243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10245 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164676 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10255 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6862 q selected
    | true =>
      simp only [d10255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10257 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164677 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164678 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro14985 (p : Pattern) (selected : d164684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1753 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro117 q selected
    | true =>
      simp only [d1753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1754 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164683 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10255 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6862 q selected
    | true =>
      simp only [d10255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10257 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164677 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164684 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro14986 (p : Pattern) (selected : d164690 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164673 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14982 q selected
    | true =>
      simp only [d164673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14983 q selected
  have h2 (q : Pattern) (selected : d164674 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164675 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164679 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14983 q selected
    | true =>
      simp only [d164679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14984 q selected
  have h5 (q : Pattern) (selected : d164680 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164681 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164682 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164685 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14983 q selected
    | true =>
      simp only [d164685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14985 q selected
  have h9 (q : Pattern) (selected : d164686 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164687 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164688 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d164689 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d164690 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d164690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro14987 (p : Pattern) (selected : d164694 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164685 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d164685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14983 q selected
    | true =>
      simp only [d164685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14985 q selected
  have h2 (q : Pattern) (selected : d164686 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d164686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164687 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d164687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164688 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d164688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164693 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d164693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164694 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d164694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14988 (p : Pattern) (selected : d164700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164691 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14986 q selected
    | true =>
      simp only [d164691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164692 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164695 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14987 q selected
    | true =>
      simp only [d164695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164696 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164697 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164698 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164699 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164700 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14989 (p : Pattern) (selected : d164704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164695 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14987 q selected
    | true =>
      simp only [d164695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164696 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164701 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164702 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164703 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164704 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14990 (p : Pattern) (selected : d164725 p = 1) : d166361 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164627 q = 1) : d164627 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d164636 q = 1) : d164636 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d164666 q = 1) : d164666 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d164705 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14988 q selected
    | true =>
      simp only [d164705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14989 q selected
  have h5 (q : Pattern) (selected : d164706 q = 1) : d166357 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164706, d166357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164706, d166357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164721 q = 1) : d164721 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d164722 q = 1) : d166358 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164722, d166358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164722, d166358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164723 q = 1) : d166359 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164723, d166359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164723, d166359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d164724 q = 1) : d166360 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164724, d166360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164724, d166360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164725 q = 1) : d166361 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164725, d166361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164725, d166361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro14991 (p : Pattern) (selected : d164740 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164691 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14986 q selected
    | true =>
      simp only [d164691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164692 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164695 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14987 q selected
    | true =>
      simp only [d164695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164696 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164697 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164698 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164699 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164740 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro14992 (p : Pattern) (selected : d164741 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164695 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d164695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14987 q selected
    | true =>
      simp only [d164695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d164696 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d164696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164701 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d164701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d164702 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d164702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164703 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d164703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164741 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d164741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro14993 (p : Pattern) (selected : d164750 p = 1) : d166366 p = 1 := by
  have h0 (q : Pattern) (selected : d164627 q = 1) : d164627 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164636 q = 1) : d164636 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d164666 q = 1) : d164666 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d164705 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14988 q selected
    | true =>
      simp only [d164705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14989 q selected
  have h4 (q : Pattern) (selected : d164706 q = 1) : d166357 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164706, d166357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164706, d166357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164721 q = 1) : d164721 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d164722 q = 1) : d166358 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164722, d166358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164722, d166358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164723 q = 1) : d166359 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164723, d166359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164723, d166359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164724 q = 1) : d166360 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164724, d166360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164724, d166360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d164731 q = 1) : d164731 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d164736 q = 1) : d164736 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d164739 q = 1) : d164739 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d164742 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14991 q selected
    | true =>
      simp only [d164742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14992 q selected
  have h13 (q : Pattern) (selected : d164743 q = 1) : d166362 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164743, d166362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d164743, d166362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d164746 q = 1) : d164746 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d164747 q = 1) : d166363 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164747, d166363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d164747, d166363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d164748 q = 1) : d166364 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164748, d166364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164748, d166364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d164749 q = 1) : d166365 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164749, d166365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d164749, d166365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d164750 q = 1) : d166366 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164750, d166366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d164750, d166366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro14994 (p : Pattern) (selected : d164775 p = 1) : d166373 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164739 q = 1) : d164739 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d164742 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d164742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14991 q selected
    | true =>
      simp only [d164742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14992 q selected
  have h3 (q : Pattern) (selected : d164743 q = 1) : d166362 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d164743, d166362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164743, d166362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164746 q = 1) : d164746 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d164747 q = 1) : d166363 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d164747, d166363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164747, d166363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164773 q = 1) : d166371 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d164773, d166371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164773, d166371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164774 q = 1) : d166372 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d164774, d166372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164774, d166372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d164775 q = 1) : d166373 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d164775, d166373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164775, d166373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro14995 (p : Pattern) (selected : d164784 p = 1) : d166380 p = 1 := by
  have h0 (q : Pattern) (selected : d164619 q = 1) : d164619 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164751 q = 1) : d166367 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d164751, d166367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14990 q selected
    | true =>
      simp only [d164751, d166367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14993 q selected
  have h2 (q : Pattern) (selected : d164769 q = 1) : d164769 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d164770 q = 1) : d166368 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d164770, d166368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d164770, d166368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d164771 q = 1) : d166369 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d164771, d166369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164771, d166369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164772 q = 1) : d166370 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d164772, d166370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164772, d166370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d164776 q = 1) : d166374 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d164776, d166374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d164776, d166374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14994 q selected
  have h8 (q : Pattern) (selected : d164778 q = 1) : d164778 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d164779 q = 1) : d166375 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d164779, d166375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164779, d166375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d164780 q = 1) : d166376 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d164780, d166376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d164780, d166376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d164781 q = 1) : d166377 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d164781, d166377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d164781, d166377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d164782 q = 1) : d166378 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d164782, d166378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d164782, d166378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d164783 q = 1) : d166379 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d164783, d166379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d164783, d166379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d164784 q = 1) : d166380 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d164784, d166380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d164784, d166380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro14996 (p : Pattern) (selected : d164790 p = 1) : d166386 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d164785 q = 1) : d166381 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d164785, d166381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164785, d166381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14995 q selected
  have h2 (q : Pattern) (selected : d164786 q = 1) : d166382 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d164786, d166382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164786, d166382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d164787 q = 1) : d166383 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d164787, d166383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164787, d166383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d164788 q = 1) : d166384 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d164788, d166384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164788, d166384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d164789 q = 1) : d166385 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d164789, d166385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164789, d166385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d164790 q = 1) : d166386 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d164790, d166386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d164790, d166386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro14997 (p : Pattern) (selected : d164900 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2201 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro148 q selected
    | true =>
      simp only [d2201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2202 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10458 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6872 q selected
    | true =>
      simp only [d10458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10460 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164898 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10468 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6873 q selected
    | true =>
      simp only [d10468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10470 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10482 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6874 q selected
    | true =>
      simp only [d10482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10484 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d164899 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d164900 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro14998 (p : Pattern) (selected : d164903 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2219 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro153 q selected
    | true =>
      simp only [d2219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2220 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10493 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6876 q selected
    | true =>
      simp only [d10493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10495 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d164901 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10482 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6874 q selected
    | true =>
      simp only [d10482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10484 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d164902 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d164902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d164903 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro14999 (p : Pattern) (selected : d164909 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10508 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6878 q selected
    | true =>
      simp only [d10508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10510 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164907 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d164907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10521 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6879 q selected
    | true =>
      simp only [d10521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10523 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d164908 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d164908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d164908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164909 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d164909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d164909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
end NetHack.Soko22Hazard87
