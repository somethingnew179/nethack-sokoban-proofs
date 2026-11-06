import NetHack.Soko22Hazard87.EqIntroBlocks0089
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro22500 (p : Pattern) (selected : d226565 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226547 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro148 q selected
  have h2 (q : Pattern) (selected : d226548 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro148 q selected
    | true =>
      simp only [d226548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226549 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226550 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226551 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6872 q selected
  have h6 (q : Pattern) (selected : d226552 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6872 q selected
    | true =>
      simp only [d226552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226553 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226554 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d226555 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d226556 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6873 q selected
  have h11 (q : Pattern) (selected : d226557 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6873 q selected
    | true =>
      simp only [d226557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d226558 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d226558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d226559 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d226559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d226560 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6874 q selected
  have h15 (q : Pattern) (selected : d226561 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6874 q selected
    | true =>
      simp only [d226561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d226562 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d226562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d226563 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d226563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d226564 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d226564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d226565 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro22501 (p : Pattern) (selected : d226576 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226566 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro153 q selected
  have h2 (q : Pattern) (selected : d226567 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro153 q selected
    | true =>
      simp only [d226567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226568 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226569 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226570 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6876 q selected
  have h6 (q : Pattern) (selected : d226571 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6876 q selected
    | true =>
      simp only [d226571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226572 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226573 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d226574 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d226560 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6874 q selected
  have h11 (q : Pattern) (selected : d226561 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6874 q selected
    | true =>
      simp only [d226561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d226562 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d226562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d226563 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d226563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d226575 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d226575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d226576 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22502 (p : Pattern) (selected : d226589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226579 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6878 q selected
  have h2 (q : Pattern) (selected : d226580 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6878 q selected
    | true =>
      simp only [d226580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226581 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226582 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226583 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226584 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6879 q selected
  have h7 (q : Pattern) (selected : d226585 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6879 q selected
    | true =>
      simp only [d226585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d226586 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d226586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d226587 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d226587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d226588 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d226589 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22503 (p : Pattern) (selected : d226598 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226593 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro154 q selected
  have h2 (q : Pattern) (selected : d226594 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro154 q selected
    | true =>
      simp only [d226594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226595 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226596 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226597 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226584 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6879 q selected
  have h7 (q : Pattern) (selected : d226585 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d226585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6879 q selected
    | true =>
      simp only [d226585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d226586 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d226586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d226586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d226587 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d226587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d226587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d226588 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d226588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d226598 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d226598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22504 (p : Pattern) (selected : d226603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226577 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22500 q selected
    | true =>
      simp only [d226577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22501 q selected
  have h2 (q : Pattern) (selected : d226578 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226590 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22501 q selected
    | true =>
      simp only [d226590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22502 q selected
  have h4 (q : Pattern) (selected : d226591 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226592 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226599 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22501 q selected
    | true =>
      simp only [d226599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22503 q selected
  have h7 (q : Pattern) (selected : d226600 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226601 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d226602 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d226602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d226603 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d226603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d226603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22505 (p : Pattern) (selected : d226607 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226599 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d226599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22501 q selected
    | true =>
      simp only [d226599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22503 q selected
  have h2 (q : Pattern) (selected : d226600 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d226600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226601 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d226601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226606 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d226606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226607 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d226607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro22506 (p : Pattern) (selected : d226613 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226604 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d226604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22504 q selected
    | true =>
      simp only [d226604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226605 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d226605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226608 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d226608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22505 q selected
    | true =>
      simp only [d226608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226609 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d226609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226610 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d226610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226611 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d226611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226612 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d226612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d226612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d226613 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d226613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d226613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22507 (p : Pattern) (selected : d226617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226608 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d226608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22505 q selected
    | true =>
      simp only [d226608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226609 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d226609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226614 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d226614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226615 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d226615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226616 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d226616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226617 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d226617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22508 (p : Pattern) (selected : d226637 p = 1) : d227621 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226546 q = 1) : d226546 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d226618 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d226618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22506 q selected
    | true =>
      simp only [d226618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22507 q selected
  have h3 (q : Pattern) (selected : d226619 q = 1) : d227617 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d226619, d227617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226619, d227617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226633 q = 1) : d226633 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d226634 q = 1) : d227618 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d226634, d227618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226634, d227618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226635 q = 1) : d227619 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d226635, d227619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226635, d227619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d226636 q = 1) : d227620 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d226636, d227620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226636, d227620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d226637 q = 1) : d227621 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d226637, d227621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226637, d227621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22509 (p : Pattern) (selected : d226654 p = 1) : d227627 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226638 q = 1) : d227622 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d226638, d227622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226638, d227622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22508 q selected
  have h2 (q : Pattern) (selected : d226649 q = 1) : d226649 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d226650 q = 1) : d227623 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d226650, d227623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226650, d227623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226651 q = 1) : d227624 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d226651, d227624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226651, d227624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226652 q = 1) : d227625 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d226652, d227625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226652, d227625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226653 q = 1) : d227626 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d226653, d227626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226653, d227626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226654 q = 1) : d227627 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d226654, d227627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226654, d227627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro22510 (p : Pattern) (selected : d226660 p = 1) : d227633 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226655 q = 1) : d227628 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d226655, d227628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226655, d227628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22509 q selected
  have h2 (q : Pattern) (selected : d226656 q = 1) : d227629 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d226656, d227629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226656, d227629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d226657 q = 1) : d227630 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d226657, d227630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226657, d227630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226658 q = 1) : d227631 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d226658, d227631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226658, d227631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d226659 q = 1) : d227632 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d226659, d227632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226659, d227632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226660 q = 1) : d227633 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d226660, d227633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226660, d227633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22511 (p : Pattern) (selected : d226666 p = 1) : d227639 p = 1 := by
  have h0 (q : Pattern) (selected : d225879 q = 1) : d227556 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d225879, d227556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22459 q selected
    | true =>
      simp only [d225879, d227556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22467 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d226018 q = 1) : d227574 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d226018, d227574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226018, d227574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22477 q selected
  have h3 (q : Pattern) (selected : d226019 q = 1) : d227575 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d226019, d227575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226019, d227575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d226229 q = 1) : d227593 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d226229, d227593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226229, d227593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22488 q selected
  have h5 (q : Pattern) (selected : d226230 q = 1) : d227594 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d226230, d227594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226230, d227594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d226231 q = 1) : d227595 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d226231, d227595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226231, d227595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d226449 q = 1) : d227613 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d226449, d227613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226449, d227613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22499 q selected
  have h8 (q : Pattern) (selected : d226450 q = 1) : d227614 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d226450, d227614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226450, d227614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d226451 q = 1) : d227615 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d226451, d227615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226451, d227615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d226452 q = 1) : d227616 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d226452, d227616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d226452, d227616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d226661 q = 1) : d227634 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d226661, d227634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226661, d227634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22510 q selected
  have h12 (q : Pattern) (selected : d226662 q = 1) : d227635 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d226662, d227635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226662, d227635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d226663 q = 1) : d227636 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d226663, d227636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226663, d227636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d226664 q = 1) : d227637 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d226664, d227637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226664, d227637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d226665 q = 1) : d227638 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d226665, d227638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d226665, d227638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d226666 q = 1) : d227639 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d226666, d227639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d226666, d227639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro22512 (p : Pattern) (selected : d226672 p = 1) : d227645 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226667 q = 1) : d227640 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d226667, d227640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22511 q selected
    | true =>
      simp only [d226667, d227640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226668 q = 1) : d227641 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d226668, d227641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226668, d227641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226669 q = 1) : d227642 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d226669, d227642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226669, d227642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226670 q = 1) : d227643 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d226670, d227643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226670, d227643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226671 q = 1) : d227644 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d226671, d227644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226671, d227644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226672 q = 1) : d227645 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d226672, d227645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226672, d227645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22513 (p : Pattern) (selected : d226678 p = 1) : d227651 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226673 q = 1) : d227646 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d226673, d227646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22512 q selected
    | true =>
      simp only [d226673, d227646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226674 q = 1) : d227647 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d226674, d227647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226674, d227647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226675 q = 1) : d227648 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d226675, d227648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226675, d227648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226676 q = 1) : d227649 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d226676, d227649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226676, d227649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226677 q = 1) : d227650 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d226677, d227650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226677, d227650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226678 q = 1) : d227651 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d226678, d227651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226678, d227651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22514 (p : Pattern) (selected : d226684 p = 1) : d227657 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226679 q = 1) : d227652 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d226679, d227652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22513 q selected
    | true =>
      simp only [d226679, d227652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226680 q = 1) : d227653 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d226680, d227653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226680, d227653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226681 q = 1) : d227654 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d226681, d227654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226681, d227654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226682 q = 1) : d227655 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d226682, d227655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226682, d227655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226683 q = 1) : d227656 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d226683, d227656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226683, d227656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226684 q = 1) : d227657 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d226684, d227657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226684, d227657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22515 (p : Pattern) (selected : d226690 p = 1) : d227663 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226685 q = 1) : d227658 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d226685, d227658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22514 q selected
    | true =>
      simp only [d226685, d227658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226686 q = 1) : d227659 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d226686, d227659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226686, d227659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226687 q = 1) : d227660 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d226687, d227660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226687, d227660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226688 q = 1) : d227661 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d226688, d227661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226688, d227661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226689 q = 1) : d227662 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d226689, d227662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226689, d227662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226690 q = 1) : d227663 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d226690, d227663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226690, d227663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22516 (p : Pattern) (selected : d226696 p = 1) : d227669 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226691 q = 1) : d227664 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d226691, d227664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22515 q selected
    | true =>
      simp only [d226691, d227664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226692 q = 1) : d227665 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d226692, d227665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226692, d227665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226693 q = 1) : d227666 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d226693, d227666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226693, d227666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226694 q = 1) : d227667 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d226694, d227667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226694, d227667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226695 q = 1) : d227668 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d226695, d227668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226695, d227668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226696 q = 1) : d227669 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d226696, d227669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226696, d227669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22517 (p : Pattern) (selected : d226702 p = 1) : d227675 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226697 q = 1) : d227670 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d226697, d227670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22516 q selected
    | true =>
      simp only [d226697, d227670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226698 q = 1) : d227671 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d226698, d227671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226698, d227671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226699 q = 1) : d227672 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d226699, d227672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226699, d227672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226700 q = 1) : d227673 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d226700, d227673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226700, d227673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226701 q = 1) : d227674 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d226701, d227674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226701, d227674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226702 q = 1) : d227675 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d226702, d227675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226702, d227675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22518 (p : Pattern) (selected : d226708 p = 1) : d227681 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d226703 q = 1) : d227676 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d226703, d227676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22517 q selected
    | true =>
      simp only [d226703, d227676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d226704 q = 1) : d227677 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d226704, d227677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d226704, d227677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d226705 q = 1) : d227678 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d226705, d227678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d226705, d227678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d226706 q = 1) : d227679 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d226706, d227679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d226706, d227679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d226707 q = 1) : d227680 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d226707, d227680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d226707, d227680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226708 q = 1) : d227681 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d226708, d227681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d226708, d227681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22519 (p : Pattern) (selected : d227689 p = 0) : d229485 p = 1 := by
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
  have h3 (q : Pattern) (selected : d21 q = 0) : d51873 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227688 q = 0) : d229484 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d227688, d229484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227688, d229484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227689 q = 0) : d229485 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d227689, d229485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227689, d229485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro22520 (p : Pattern) (selected : d227695 p = 0) : d229491 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227690 q = 0) : d229486 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227690, d229486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22519 q selected
    | true =>
      simp only [d227690, d229486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227691 q = 0) : d229487 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227691, d229487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227691, d229487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d227692 q = 0) : d229488 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227692, d229488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227692, d229488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227693 q = 0) : d229489 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227693, d229489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227693, d229489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227694 q = 0) : d229490 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d227694, d229490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227694, d229490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d227695 q = 0) : d229491 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d227695, d229491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227695, d229491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22521 (p : Pattern) (selected : d227701 p = 0) : d229497 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227696 q = 0) : d229492 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d227696, d229492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22520 q selected
    | true =>
      simp only [d227696, d229492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227697 q = 0) : d229493 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d227697, d229493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227697, d229493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227698 q = 0) : d229494 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d227698, d229494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227698, d229494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227699 q = 0) : d229495 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d227699, d229495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227699, d229495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227700 q = 0) : d229496 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d227700, d229496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227700, d229496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d227701 q = 0) : d229497 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d227701, d229497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227701, d229497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22522 (p : Pattern) (selected : d227707 p = 0) : d229503 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227702 q = 0) : d229498 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227702, d229498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22521 q selected
    | true =>
      simp only [d227702, d229498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227703 q = 0) : d229499 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227703, d229499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227703, d229499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227704 q = 0) : d229500 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d227704, d229500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227704, d229500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227705 q = 0) : d229501 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d227705, d229501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227705, d229501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227706 q = 0) : d229502 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d227706, d229502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227706, d229502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d227707 q = 0) : d229503 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d227707, d229503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227707, d229503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22523 (p : Pattern) (selected : d227713 p = 0) : d229509 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227708 q = 0) : d229504 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227708, d229504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22522 q selected
    | true =>
      simp only [d227708, d229504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227709 q = 0) : d229505 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227709, d229505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227709, d229505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d227710 q = 0) : d229506 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d227710, d229506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227710, d229506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227711 q = 0) : d229507 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d227711, d229507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227711, d229507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d227712 q = 0) : d229508 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d227712, d229508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227712, d229508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227713 q = 0) : d229509 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d227713, d229509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227713, d229509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22524 (p : Pattern) (selected : d227714 p = 0) : d229510 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227702 q = 0) : d229498 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227702, d229498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22521 q selected
    | true =>
      simp only [d227702, d229498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227703 q = 0) : d229499 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227703, d229499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227703, d229499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227704 q = 0) : d229500 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d227704, d229500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227704, d229500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227705 q = 0) : d229501 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d227705, d229501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227705, d229501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227706 q = 0) : d229502 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d227706, d229502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227706, d229502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d227714 q = 0) : d229510 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d227714, d229510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227714, d229510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22525 (p : Pattern) (selected : d227720 p = 0) : d229516 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227708 q = 0) : d229504 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227708, d229504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22522 q selected
    | true =>
      simp only [d227708, d229504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227709 q = 0) : d229505 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227709, d229505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227709, d229505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d227710 q = 0) : d229506 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d227710, d229506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227710, d229506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227711 q = 0) : d229507 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d227711, d229507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227711, d229507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d227712 q = 0) : d229508 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d227712, d229508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227712, d229508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227715 q = 0) : d229511 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227715, d229511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22524 q selected
    | true =>
      simp only [d227715, d229511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d227716 q = 0) : d229512 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227716, d229512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d227716, d229512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d227717 q = 0) : d229513 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d227717, d229513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227717, d229513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d227718 q = 0) : d229514 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d227718, d229514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227718, d229514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227719 q = 0) : d229515 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d227719, d229515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227719, d229515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d227720 q = 0) : d229516 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d227720, d229516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227720, d229516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22526 (p : Pattern) (selected : d227725 p = 0) : d229521 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227715 q = 0) : d229511 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227715, d229511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22524 q selected
    | true =>
      simp only [d227715, d229511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227716 q = 0) : d229512 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227716, d229512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227716, d229512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d227717 q = 0) : d229513 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d227717, d229513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227717, d229513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227718 q = 0) : d229514 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d227718, d229514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227718, d229514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d227719 q = 0) : d229515 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d227719, d229515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227719, d229515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227725 q = 0) : d229521 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d227725, d229521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227725, d229521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22527 (p : Pattern) (selected : d227736 p = 0) : d229532 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227731 q = 0) : d229527 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227731, d229527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227731, d229527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22519 q selected
  have h2 (q : Pattern) (selected : d227690 q = 0) : d229486 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227690, d229486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22519 q selected
    | true =>
      simp only [d227690, d229486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d227732 q = 0) : d229528 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227732, d229528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227732, d229528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227691 q = 0) : d229487 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227691, d229487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227691, d229487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227733 q = 0) : d229529 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227733, d229529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227733, d229529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227734 q = 0) : d229530 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227734, d229530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227734, d229530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d227735 q = 0) : d229531 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d227735, d229531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d227735, d229531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d227736 q = 0) : d229532 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d227736, d229532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227736, d229532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22528 (p : Pattern) (selected : d227742 p = 0) : d229538 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227737 q = 0) : d229533 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d227737, d229533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22527 q selected
    | true =>
      simp only [d227737, d229533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227738 q = 0) : d229534 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d227738, d229534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227738, d229534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227739 q = 0) : d229535 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d227739, d229535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227739, d229535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227740 q = 0) : d229536 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d227740, d229536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227740, d229536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227741 q = 0) : d229537 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d227741, d229537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227741, d229537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d227742 q = 0) : d229538 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d227742, d229538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227742, d229538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22529 (p : Pattern) (selected : d227748 p = 0) : d229544 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227743 q = 0) : d229539 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227743, d229539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22528 q selected
    | true =>
      simp only [d227743, d229539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227744 q = 0) : d229540 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227744, d229540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227744, d229540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227745 q = 0) : d229541 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d227745, d229541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227745, d229541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227746 q = 0) : d229542 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d227746, d229542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227746, d229542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227747 q = 0) : d229543 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d227747, d229543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227747, d229543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d227748 q = 0) : d229544 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d227748, d229544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227748, d229544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22530 (p : Pattern) (selected : d227754 p = 0) : d229550 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227749 q = 0) : d229545 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227749, d229545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22529 q selected
    | true =>
      simp only [d227749, d229545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227750 q = 0) : d229546 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227750, d229546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227750, d229546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d227751 q = 0) : d229547 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d227751, d229547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227751, d229547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227752 q = 0) : d229548 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d227752, d229548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227752, d229548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d227753 q = 0) : d229549 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d227753, d229549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227753, d229549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227754 q = 0) : d229550 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d227754, d229550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227754, d229550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22531 (p : Pattern) (selected : d227760 p = 0) : d229556 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227721 q = 0) : d229517 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d227721, d229517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22523 q selected
    | true =>
      simp only [d227721, d229517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22525 q selected
  have h2 (q : Pattern) (selected : d227722 q = 0) : d229518 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d227722, d229518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227722, d229518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d227723 q = 0) : d229519 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d227723, d229519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227723, d229519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227724 q = 0) : d229520 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d227724, d229520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227724, d229520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d227726 q = 0) : d229522 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d227726, d229522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227726, d229522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22526 q selected
  have h6 (q : Pattern) (selected : d227727 q = 0) : d229523 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d227727, d229523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227727, d229523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d227728 q = 0) : d229524 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d227728, d229524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d227728, d229524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d227729 q = 0) : d229525 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d227729, d229525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227729, d229525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d227730 q = 0) : d229526 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d227730, d229526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227730, d229526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227755 q = 0) : d229551 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d227755, d229551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227755, d229551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22530 q selected
  have h11 (q : Pattern) (selected : d227756 q = 0) : d229552 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d227756, d229552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d227756, d229552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d227757 q = 0) : d229553 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d227757, d229553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d227757, d229553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d227758 q = 0) : d229554 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d227758, d229554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d227758, d229554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d227759 q = 0) : d229555 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d227759, d229555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d227759, d229555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d227760 q = 0) : d229556 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d227760, d229556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d227760, d229556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22532 (p : Pattern) (selected : d227770 p = 0) : d229566 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227708 q = 0) : d229504 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227708, d229504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22522 q selected
    | true =>
      simp only [d227708, d229504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227766 q = 0) : d229562 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227766, d229562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227766, d229562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227767 q = 0) : d229563 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d227767, d229563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227767, d229563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227768 q = 0) : d229564 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d227768, d229564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227768, d229564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d227769 q = 0) : d229565 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d227769, d229565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227769, d229565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227770 q = 0) : d229566 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d227770, d229566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227770, d229566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22533 (p : Pattern) (selected : d227777 p = 0) : d229573 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227708 q = 0) : d229504 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227708, d229504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22522 q selected
    | true =>
      simp only [d227708, d229504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227766 q = 0) : d229562 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227766, d229562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227766, d229562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227767 q = 0) : d229563 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d227767, d229563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227767, d229563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227768 q = 0) : d229564 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d227768, d229564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227768, d229564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d227769 q = 0) : d229565 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d227769, d229565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227769, d229565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227715 q = 0) : d229511 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227715, d229511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22524 q selected
    | true =>
      simp only [d227715, d229511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d227773 q = 0) : d229569 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227773, d229569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227773, d229569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d227774 q = 0) : d229570 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d227774, d229570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227774, d229570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d227775 q = 0) : d229571 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d227775, d229571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227775, d229571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227776 q = 0) : d229572 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d227776, d229572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227776, d229572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d227777 q = 0) : d229573 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d227777, d229573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227777, d229573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22534 (p : Pattern) (selected : d227782 p = 0) : d229578 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227702 q = 0) : d229498 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227702, d229498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22521 q selected
    | true =>
      simp only [d227702, d229498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227703 q = 0) : d229499 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227703, d229499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227703, d229499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227704 q = 0) : d229500 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d227704, d229500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227704, d229500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227705 q = 0) : d229501 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d227705, d229501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227705, d229501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227781 q = 0) : d229577 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d227781, d229577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227781, d229577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227782 q = 0) : d229578 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d227782, d229578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227782, d229578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22535 (p : Pattern) (selected : d227789 p = 0) : d229585 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227702 q = 0) : d229498 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227702, d229498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22521 q selected
    | true =>
      simp only [d227702, d229498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227703 q = 0) : d229499 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227703, d229499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227703, d229499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227704 q = 0) : d229500 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d227704, d229500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227704, d229500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227787 q = 0) : d229583 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d227787, d229583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227787, d229583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d227788 q = 0) : d229584 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d227788, d229584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227788, d229584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d227789 q = 0) : d229585 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d227789, d229585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227789, d229585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22536 (p : Pattern) (selected : d227794 p = 0) : d229590 p = 1 := by
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
  have h3 (q : Pattern) (selected : d19 q = 0) : d51871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20 q = 0) : d51872 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d135 q = 0) : d51986 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d51986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d135, d51986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227793 q = 0) : d229589 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d227793, d229589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227793, d229589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d21 q = 0) : d51873 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d227688 q = 0) : d229484 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d227688, d229484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227688, d229484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d227794 q = 0) : d229590 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d227794, d229590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d227794, d229590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro22537 (p : Pattern) (selected : d227800 p = 0) : d229596 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227795 q = 0) : d229591 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227795, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22536 q selected
    | true =>
      simp only [d227795, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227796 q = 0) : d229592 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227796, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227796, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d227797 q = 0) : d229593 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227797, d229593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227797, d229593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227798 q = 0) : d229594 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227798, d229594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227798, d229594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227690 q = 0) : d229486 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227690, d229486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22519 q selected
    | true =>
      simp only [d227690, d229486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d227691 q = 0) : d229487 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227691, d229487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227691, d229487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d227692 q = 0) : d229488 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227692, d229488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227692, d229488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d227693 q = 0) : d229489 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227693, d229489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227693, d229489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d227799 q = 0) : d229595 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d227799, d229595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227799, d229595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227694 q = 0) : d229490 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d227694, d229490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d227694, d229490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d227800 q = 0) : d229596 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d227800, d229596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d227800, d229596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22538 (p : Pattern) (selected : d227806 p = 0) : d229602 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227801 q = 0) : d229597 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d227801, d229597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22537 q selected
    | true =>
      simp only [d227801, d229597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22520 q selected
  have h2 (q : Pattern) (selected : d227802 q = 0) : d229598 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d227802, d229598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227802, d229598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227803 q = 0) : d229599 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d227803, d229599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227803, d229599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227696 q = 0) : d229492 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d227696, d229492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22520 q selected
    | true =>
      simp only [d227696, d229492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227697 q = 0) : d229493 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d227697, d229493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227697, d229493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227698 q = 0) : d229494 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d227698, d229494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227698, d229494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d227804 q = 0) : d229600 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d227804, d229600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227804, d229600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d227699 q = 0) : d229495 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d227699, d229495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d227699, d229495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d227805 q = 0) : d229601 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d227805, d229601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227805, d229601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227806 q = 0) : d229602 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d227806, d229602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d227806, d229602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22539 (p : Pattern) (selected : d227812 p = 0) : d229608 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227807 q = 0) : d229603 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227807, d229603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22538 q selected
    | true =>
      simp only [d227807, d229603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227808 q = 0) : d229604 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227808, d229604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227808, d229604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227702 q = 0) : d229498 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227702, d229498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22521 q selected
    | true =>
      simp only [d227702, d229498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227703 q = 0) : d229499 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227703, d229499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227703, d229499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d227809 q = 0) : d229605 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d227809, d229605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227809, d229605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227810 q = 0) : d229606 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d227810, d229606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227810, d229606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d227811 q = 0) : d229607 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d227811, d229607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d227811, d229607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d227812 q = 0) : d229608 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d227812, d229608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227812, d229608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22540 (p : Pattern) (selected : d227815 p = 0) : d229485 p = 1 := by
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
  have h3 (q : Pattern) (selected : d166 q = 0) : d51873 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d166, d51873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d166, d51873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227814 q = 0) : d229484 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d227814, d229484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227814, d229484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227815 q = 0) : d229485 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d227815, d229485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227815, d229485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro22541 (p : Pattern) (selected : d227821 p = 0) : d229491 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227816 q = 0) : d229486 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227816, d229486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22540 q selected
    | true =>
      simp only [d227816, d229486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227817 q = 0) : d229487 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227817, d229487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227817, d229487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d227818 q = 0) : d229488 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227818, d229488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227818, d229488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227819 q = 0) : d229489 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227819, d229489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227819, d229489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227820 q = 0) : d229490 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d227820, d229490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227820, d229490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d227821 q = 0) : d229491 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d227821, d229491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227821, d229491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22542 (p : Pattern) (selected : d227827 p = 0) : d229497 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227822 q = 0) : d229492 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d227822, d229492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22541 q selected
    | true =>
      simp only [d227822, d229492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227823 q = 0) : d229493 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d227823, d229493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227823, d229493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227824 q = 0) : d229494 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d227824, d229494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227824, d229494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227825 q = 0) : d229495 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d227825, d229495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227825, d229495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227826 q = 0) : d229496 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d227826, d229496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227826, d229496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d227827 q = 0) : d229497 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d227827, d229497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227827, d229497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22543 (p : Pattern) (selected : d227833 p = 0) : d229503 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227828 q = 0) : d229498 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227828, d229498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22542 q selected
    | true =>
      simp only [d227828, d229498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227829 q = 0) : d229499 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227829, d229499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227829, d229499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227830 q = 0) : d229500 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d227830, d229500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227830, d229500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227831 q = 0) : d229501 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d227831, d229501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227831, d229501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227832 q = 0) : d229502 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d227832, d229502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227832, d229502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d227833 q = 0) : d229503 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d227833, d229503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227833, d229503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22544 (p : Pattern) (selected : d227839 p = 0) : d229614 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227783 q = 0) : d229579 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227783, d229579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22534 q selected
    | true =>
      simp only [d227783, d229579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227784 q = 0) : d229580 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227784, d229580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227784, d229580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227785 q = 0) : d229581 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d227785, d229581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227785, d229581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227786 q = 0) : d229582 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d227786, d229582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227786, d229582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d227790 q = 0) : d229586 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227790, d229586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22535 q selected
    | true =>
      simp only [d227790, d229586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d227791 q = 0) : d229587 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227791, d229587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227791, d229587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d227792 q = 0) : d229588 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d227792, d229588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d227792, d229588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d227813 q = 0) : d229609 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227813, d229609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22539 q selected
    | true =>
      simp only [d227813, d229609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22522 q selected
  have h9 (q : Pattern) (selected : d227834 q = 0) : d229504 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227834, d229504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22543 q selected
    | true =>
      simp only [d227834, d229504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d227835 q = 0) : d229610 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227835, d229610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d227835, d229610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d227708 q = 0) : d229504 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227708, d229504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22522 q selected
    | true =>
      simp only [d227708, d229504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d227709 q = 0) : d229505 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227709, d229505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d227709, d229505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d227836 q = 0) : d229611 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d227836, d229611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d227836, d229611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d227837 q = 0) : d229612 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d227837, d229612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227837, d229612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d227838 q = 0) : d229613 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d227838, d229613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227838, d229613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d227839 q = 0) : d229614 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d227839, d229614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227839, d229614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro22545 (p : Pattern) (selected : d227840 p = 0) : d229615 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227702 q = 0) : d229498 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227702, d229498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22521 q selected
    | true =>
      simp only [d227702, d229498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227703 q = 0) : d229499 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227703, d229499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227703, d229499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227704 q = 0) : d229500 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d227704, d229500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227704, d229500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227705 q = 0) : d229501 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d227705, d229501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227705, d229501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227781 q = 0) : d229577 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d227781, d229577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227781, d229577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227840 q = 0) : d229615 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d227840, d229615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227840, d229615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22546 (p : Pattern) (selected : d227845 p = 0) : d229620 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227702 q = 0) : d229498 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227702, d229498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22521 q selected
    | true =>
      simp only [d227702, d229498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227703 q = 0) : d229499 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227703, d229499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227703, d229499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227704 q = 0) : d229500 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d227704, d229500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227704, d229500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227787 q = 0) : d229583 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d227787, d229583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227787, d229583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d227788 q = 0) : d229584 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d227788, d229584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227788, d229584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d227845 q = 0) : d229620 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d227845, d229620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227845, d229620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22547 (p : Pattern) (selected : d227849 p = 0) : d229624 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227807 q = 0) : d229603 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227807, d229603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22538 q selected
    | true =>
      simp only [d227807, d229603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227808 q = 0) : d229604 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227808, d229604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227808, d229604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227702 q = 0) : d229498 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227702, d229498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22521 q selected
    | true =>
      simp only [d227702, d229498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227703 q = 0) : d229499 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227703, d229499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227703, d229499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d227809 q = 0) : d229605 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d227809, d229605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227809, d229605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227810 q = 0) : d229606 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d227810, d229606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227810, d229606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d227811 q = 0) : d229607 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d227811, d229607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d227811, d229607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d227849 q = 0) : d229624 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d227849, d229624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227849, d229624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22548 (p : Pattern) (selected : d227851 p = 0) : d229510 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227828 q = 0) : d229498 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227828, d229498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22542 q selected
    | true =>
      simp only [d227828, d229498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227829 q = 0) : d229499 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227829, d229499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227829, d229499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227830 q = 0) : d229500 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d227830, d229500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227830, d229500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227831 q = 0) : d229501 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d227831, d229501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227831, d229501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227832 q = 0) : d229502 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d227832, d229502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227832, d229502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d227851 q = 0) : d229510 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d227851, d229510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227851, d229510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22549 (p : Pattern) (selected : d227857 p = 0) : d229630 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227783 q = 0) : d229579 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227783, d229579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22534 q selected
    | true =>
      simp only [d227783, d229579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227784 q = 0) : d229580 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227784, d229580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227784, d229580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227785 q = 0) : d229581 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d227785, d229581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227785, d229581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227786 q = 0) : d229582 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d227786, d229582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227786, d229582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d227790 q = 0) : d229586 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227790, d229586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22535 q selected
    | true =>
      simp only [d227790, d229586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d227791 q = 0) : d229587 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227791, d229587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227791, d229587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d227792 q = 0) : d229588 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d227792, d229588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d227792, d229588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d227813 q = 0) : d229609 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227813, d229609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22539 q selected
    | true =>
      simp only [d227813, d229609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22522 q selected
  have h9 (q : Pattern) (selected : d227834 q = 0) : d229504 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227834, d229504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22543 q selected
    | true =>
      simp only [d227834, d229504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d227835 q = 0) : d229610 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227835, d229610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d227835, d229610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d227708 q = 0) : d229504 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227708, d229504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22522 q selected
    | true =>
      simp only [d227708, d229504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d227709 q = 0) : d229505 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227709, d229505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d227709, d229505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d227836 q = 0) : d229611 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d227836, d229611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d227836, d229611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d227837 q = 0) : d229612 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d227837, d229612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227837, d229612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d227838 q = 0) : d229613 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d227838, d229613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227838, d229613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d227841 q = 0) : d229616 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227841, d229616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22545 q selected
    | true =>
      simp only [d227841, d229616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d227842 q = 0) : d229617 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227842, d229617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227842, d229617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d227843 q = 0) : d229618 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d227843, d229618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d227843, d229618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d227844 q = 0) : d229619 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d227844, d229619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227844, d229619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d227846 q = 0) : d229621 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227846, d229621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22546 q selected
    | true =>
      simp only [d227846, d229621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d227847 q = 0) : d229622 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227847, d229622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227847, d229622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d227848 q = 0) : d229623 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d227848, d229623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d227848, d229623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d227850 q = 0) : d229625 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227850, d229625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22547 q selected
    | true =>
      simp only [d227850, d229625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22524 q selected
  have h24 (q : Pattern) (selected : d227852 q = 0) : d229511 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227852, d229511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22548 q selected
    | true =>
      simp only [d227852, d229511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d227853 q = 0) : d229626 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227853, d229626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d227853, d229626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d227715 q = 0) : d229511 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227715, d229511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22524 q selected
    | true =>
      simp only [d227715, d229511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d227716 q = 0) : d229512 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227716, d229512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d227716, d229512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d227854 q = 0) : d229627 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d227854, d229627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d227854, d229627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d227855 q = 0) : d229628 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d227855, d229628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d227855, d229628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d227856 q = 0) : d229629 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d227856, d229629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d227856, d229629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d227857 q = 0) : d229630 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d227857, d229630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d227857, d229630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro22550 (p : Pattern) (selected : d227859 p = 0) : d229632 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227708 q = 0) : d229504 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227708, d229504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22522 q selected
    | true =>
      simp only [d227708, d229504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227766 q = 0) : d229562 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227766, d229562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227766, d229562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227767 q = 0) : d229563 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d227767, d229563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227767, d229563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227768 q = 0) : d229564 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d227768, d229564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227768, d229564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d227769 q = 0) : d229565 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d227769, d229565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227769, d229565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227859 q = 0) : d229632 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d227859, d229632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227859, d229632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22551 (p : Pattern) (selected : d227866 p = 0) : d229639 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227850 q = 0) : d229625 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227850, d229625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22547 q selected
    | true =>
      simp only [d227850, d229625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22524 q selected
  have h2 (q : Pattern) (selected : d227852 q = 0) : d229511 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227852, d229511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22548 q selected
    | true =>
      simp only [d227852, d229511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d227853 q = 0) : d229626 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227853, d229626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227853, d229626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227715 q = 0) : d229511 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227715, d229511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22524 q selected
    | true =>
      simp only [d227715, d229511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227716 q = 0) : d229512 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227716, d229512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227716, d229512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d227854 q = 0) : d229627 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d227854, d229627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227854, d229627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d227864 q = 0) : d229637 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d227864, d229637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227864, d229637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d227865 q = 0) : d229638 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d227865, d229638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227865, d229638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d227866 q = 0) : d229639 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d227866, d229639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227866, d229639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro22552 (p : Pattern) (selected : d227877 p = 0) : d229650 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227872 q = 0) : d229645 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227872, d229645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227872, d229645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22536 q selected
  have h2 (q : Pattern) (selected : d227795 q = 0) : d229591 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227795, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22536 q selected
    | true =>
      simp only [d227795, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d227873 q = 0) : d229646 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227873, d229646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227873, d229646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227796 q = 0) : d229592 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227796, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227796, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227874 q = 0) : d229647 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227874, d229647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227874, d229647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227875 q = 0) : d229648 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227875, d229648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227875, d229648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d227731 q = 0) : d229527 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227731, d229527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227731, d229527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22519 q selected
  have h8 (q : Pattern) (selected : d227690 q = 0) : d229486 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227690, d229486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22519 q selected
    | true =>
      simp only [d227690, d229486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d227732 q = 0) : d229528 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227732, d229528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227732, d229528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227691 q = 0) : d229487 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227691, d229487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d227691, d229487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d227733 q = 0) : d229529 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227733, d229529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d227733, d229529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d227734 q = 0) : d229530 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227734, d229530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d227734, d229530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d227876 q = 0) : d229649 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d227876, d229649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d227876, d229649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d227735 q = 0) : d229531 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d227735, d229531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d227735, d229531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d227877 q = 0) : d229650 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d227877, d229650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d227877, d229650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22553 (p : Pattern) (selected : d227883 p = 0) : d229656 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227878 q = 0) : d229651 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d227878, d229651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22552 q selected
    | true =>
      simp only [d227878, d229651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22527 q selected
  have h2 (q : Pattern) (selected : d227879 q = 0) : d229652 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d227879, d229652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227879, d229652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227880 q = 0) : d229653 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d227880, d229653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227880, d229653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227737 q = 0) : d229533 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d227737, d229533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22527 q selected
    | true =>
      simp only [d227737, d229533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227738 q = 0) : d229534 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d227738, d229534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227738, d229534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227739 q = 0) : d229535 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d227739, d229535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227739, d229535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d227881 q = 0) : d229654 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d227881, d229654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227881, d229654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d227740 q = 0) : d229536 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d227740, d229536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d227740, d229536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d227882 q = 0) : d229655 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d227882, d229655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227882, d229655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227883 q = 0) : d229656 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d227883, d229656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d227883, d229656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22554 (p : Pattern) (selected : d227889 p = 0) : d229662 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227884 q = 0) : d229657 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227884, d229657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22553 q selected
    | true =>
      simp only [d227884, d229657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227885 q = 0) : d229658 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227885, d229658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227885, d229658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227743 q = 0) : d229539 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227743, d229539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22528 q selected
    | true =>
      simp only [d227743, d229539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227744 q = 0) : d229540 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227744, d229540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227744, d229540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d227886 q = 0) : d229659 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d227886, d229659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227886, d229659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227887 q = 0) : d229660 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d227887, d229660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227887, d229660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d227888 q = 0) : d229661 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d227888, d229661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d227888, d229661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d227889 q = 0) : d229662 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d227889, d229662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227889, d229662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22555 (p : Pattern) (selected : d227896 p = 0) : d229532 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227891 q = 0) : d229527 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227891, d229527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227891, d229527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22540 q selected
  have h2 (q : Pattern) (selected : d227816 q = 0) : d229486 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227816, d229486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22540 q selected
    | true =>
      simp only [d227816, d229486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d227892 q = 0) : d229528 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227892, d229528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227892, d229528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227817 q = 0) : d229487 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227817, d229487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227817, d229487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227893 q = 0) : d229529 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227893, d229529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227893, d229529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227894 q = 0) : d229530 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227894, d229530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227894, d229530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d227895 q = 0) : d229531 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d227895, d229531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d227895, d229531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d227896 q = 0) : d229532 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d227896, d229532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227896, d229532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22556 (p : Pattern) (selected : d227902 p = 0) : d229538 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227897 q = 0) : d229533 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d227897, d229533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22555 q selected
    | true =>
      simp only [d227897, d229533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227898 q = 0) : d229534 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d227898, d229534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227898, d229534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227899 q = 0) : d229535 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d227899, d229535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227899, d229535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227900 q = 0) : d229536 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d227900, d229536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227900, d229536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227901 q = 0) : d229537 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d227901, d229537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227901, d229537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d227902 q = 0) : d229538 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d227902, d229538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227902, d229538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22557 (p : Pattern) (selected : d227908 p = 0) : d229544 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227903 q = 0) : d229539 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227903, d229539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22556 q selected
    | true =>
      simp only [d227903, d229539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227904 q = 0) : d229540 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227904, d229540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227904, d229540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227905 q = 0) : d229541 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d227905, d229541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227905, d229541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227906 q = 0) : d229542 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d227906, d229542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227906, d229542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227907 q = 0) : d229543 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d227907, d229543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227907, d229543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d227908 q = 0) : d229544 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d227908, d229544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227908, d229544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22558 (p : Pattern) (selected : d227914 p = 0) : d229668 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227890 q = 0) : d229663 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227890, d229663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22554 q selected
    | true =>
      simp only [d227890, d229663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22529 q selected
  have h2 (q : Pattern) (selected : d227909 q = 0) : d229545 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227909, d229545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22557 q selected
    | true =>
      simp only [d227909, d229545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d227910 q = 0) : d229664 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227910, d229664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227910, d229664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227749 q = 0) : d229545 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227749, d229545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22529 q selected
    | true =>
      simp only [d227749, d229545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227750 q = 0) : d229546 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227750, d229546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227750, d229546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d227911 q = 0) : d229665 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d227911, d229665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227911, d229665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d227912 q = 0) : d229666 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d227912, d229666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227912, d229666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d227913 q = 0) : d229667 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d227913, d229667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227913, d229667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d227914 q = 0) : d229668 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d227914, d229668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227914, d229668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro22559 (p : Pattern) (selected : d227920 p = 0) : d229674 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227771 q = 0) : d229567 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d227771, d229567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227771, d229567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22532 q selected
  have h2 (q : Pattern) (selected : d227772 q = 0) : d229568 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d227772, d229568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227772, d229568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d227778 q = 0) : d229574 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d227778, d229574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22532 q selected
    | true =>
      simp only [d227778, d229574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22533 q selected
  have h4 (q : Pattern) (selected : d227779 q = 0) : d229575 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d227779, d229575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227779, d229575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227780 q = 0) : d229576 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d227780, d229576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227780, d229576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227858 q = 0) : d229631 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d227858, d229631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22544 q selected
    | true =>
      simp only [d227858, d229631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22549 q selected
  have h7 (q : Pattern) (selected : d227860 q = 0) : d229633 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d227860, d229633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22550 q selected
    | true =>
      simp only [d227860, d229633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d227861 q = 0) : d229634 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d227861, d229634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d227861, d229634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d227862 q = 0) : d229635 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d227862, d229635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d227862, d229635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d227863 q = 0) : d229636 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d227863, d229636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227863, d229636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d227867 q = 0) : d229640 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d227867, d229640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227867, d229640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22551 q selected
  have h12 (q : Pattern) (selected : d227868 q = 0) : d229641 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d227868, d229641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d227868, d229641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d227869 q = 0) : d229642 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d227869, d229642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d227869, d229642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d227870 q = 0) : d229643 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d227870, d229643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d227870, d229643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d227871 q = 0) : d229644 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d227871, d229644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d227871, d229644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d227915 q = 0) : d229669 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d227915, d229669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227915, d229669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22558 q selected
  have h17 (q : Pattern) (selected : d227916 q = 0) : d229670 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d227916, d229670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d227916, d229670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d227917 q = 0) : d229671 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d227917, d229671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d227917, d229671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d227918 q = 0) : d229672 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d227918, d229672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d227918, d229672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d227919 q = 0) : d229673 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d227919, d229673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d227919, d229673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d227920 q = 0) : d229674 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d227920, d229674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d227920, d229674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro22560 (p : Pattern) (selected : d227926 p = 0) : d229680 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227761 q = 0) : d229557 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d227761, d229557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227761, d229557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22531 q selected
  have h2 (q : Pattern) (selected : d227762 q = 0) : d229558 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d227762, d229558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227762, d229558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227763 q = 0) : d229559 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d227763, d229559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227763, d229559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227764 q = 0) : d229560 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d227764, d229560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227764, d229560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d227765 q = 0) : d229561 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d227765, d229561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227765, d229561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227921 q = 0) : d229675 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d227921, d229675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227921, d229675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22559 q selected
  have h7 (q : Pattern) (selected : d227922 q = 0) : d229676 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d227922, d229676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227922, d229676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d227923 q = 0) : d229677 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d227923, d229677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227923, d229677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d227924 q = 0) : d229678 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d227924, d229678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227924, d229678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227925 q = 0) : d229679 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d227925, d229679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227925, d229679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d227926 q = 0) : d229680 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d227926, d229680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227926, d229680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22561 (p : Pattern) (selected : d227931 p = 0) : d229685 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227813 q = 0) : d229609 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227813, d229609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22539 q selected
    | true =>
      simp only [d227813, d229609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22522 q selected
  have h2 (q : Pattern) (selected : d227927 q = 0) : d229681 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227927, d229681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227927, d229681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227928 q = 0) : d229682 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d227928, d229682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227928, d229682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227929 q = 0) : d229683 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d227929, d229683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227929, d229683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d227930 q = 0) : d229684 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d227930, d229684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227930, d229684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227931 q = 0) : d229685 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d227931, d229685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227931, d229685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22562 (p : Pattern) (selected : d227938 p = 0) : d229692 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227813 q = 0) : d229609 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227813, d229609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22539 q selected
    | true =>
      simp only [d227813, d229609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22522 q selected
  have h2 (q : Pattern) (selected : d227927 q = 0) : d229681 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227927, d229681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227927, d229681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227928 q = 0) : d229682 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d227928, d229682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227928, d229682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227929 q = 0) : d229683 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d227929, d229683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227929, d229683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d227930 q = 0) : d229684 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d227930, d229684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227930, d229684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227850 q = 0) : d229625 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227850, d229625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22547 q selected
    | true =>
      simp only [d227850, d229625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22524 q selected
  have h7 (q : Pattern) (selected : d227934 q = 0) : d229688 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227934, d229688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227934, d229688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d227935 q = 0) : d229689 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d227935, d229689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227935, d229689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d227936 q = 0) : d229690 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d227936, d229690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227936, d229690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227937 q = 0) : d229691 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d227937, d229691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227937, d229691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d227938 q = 0) : d229692 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d227938, d229692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227938, d229692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22563 (p : Pattern) (selected : d227943 p = 0) : d229697 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227807 q = 0) : d229603 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227807, d229603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22538 q selected
    | true =>
      simp only [d227807, d229603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227808 q = 0) : d229604 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227808, d229604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227808, d229604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227702 q = 0) : d229498 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227702, d229498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22521 q selected
    | true =>
      simp only [d227702, d229498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227703 q = 0) : d229499 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227703, d229499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227703, d229499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d227809 q = 0) : d229605 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d227809, d229605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227809, d229605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227810 q = 0) : d229606 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d227810, d229606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227810, d229606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d227942 q = 0) : d229696 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d227942, d229696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227942, d229696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d227943 q = 0) : d229697 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d227943, d229697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227943, d229697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22564 (p : Pattern) (selected : d227950 p = 0) : d229704 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227807 q = 0) : d229603 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227807, d229603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22538 q selected
    | true =>
      simp only [d227807, d229603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227808 q = 0) : d229604 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227808, d229604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227808, d229604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227702 q = 0) : d229498 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227702, d229498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22521 q selected
    | true =>
      simp only [d227702, d229498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227703 q = 0) : d229499 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227703, d229499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227703, d229499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d227809 q = 0) : d229605 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d227809, d229605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227809, d229605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227948 q = 0) : d229702 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d227948, d229702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227948, d229702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d227949 q = 0) : d229703 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d227949, d229703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d227949, d229703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d227950 q = 0) : d229704 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d227950, d229704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227950, d229704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22565 (p : Pattern) (selected : d227955 p = 0) : d229709 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d537 q = 0) : d52284 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d537, d52284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro276 q selected
    | true =>
      simp only [d537, d52284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d538 q = 0) : d52285 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d538, d52285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d538, d52285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d133 q = 0) : d51984 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro204 q selected
    | true =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d134 q = 0) : d51985 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d539 q = 0) : d52286 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d539, d52286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d539, d52286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227954 q = 0) : d229708 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d227954, d229708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227954, d229708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d19 q = 0) : d51871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d20 q = 0) : d51872 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d135 q = 0) : d51986 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d51986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d135, d51986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227793 q = 0) : d229589 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d227793, d229589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d227793, d229589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d227955 q = 0) : d229709 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d227955, d229709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d227955, d229709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22566 (p : Pattern) (selected : d227961 p = 0) : d229715 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227956 q = 0) : d229710 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227956, d229710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22565 q selected
    | true =>
      simp only [d227956, d229710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227957 q = 0) : d229711 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227957, d229711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227957, d229711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d227958 q = 0) : d229712 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227958, d229712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227958, d229712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227959 q = 0) : d229713 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227959, d229713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227959, d229713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227795 q = 0) : d229591 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227795, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22536 q selected
    | true =>
      simp only [d227795, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d227796 q = 0) : d229592 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227796, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227796, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d227797 q = 0) : d229593 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227797, d229593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227797, d229593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d227798 q = 0) : d229594 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227798, d229594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227798, d229594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d227960 q = 0) : d229714 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d227960, d229714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227960, d229714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227690 q = 0) : d229486 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227690, d229486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22519 q selected
    | true =>
      simp only [d227690, d229486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d227691 q = 0) : d229487 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227691, d229487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d227691, d229487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d227692 q = 0) : d229488 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227692, d229488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227692, d229488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d227693 q = 0) : d229489 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227693, d229489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d227693, d229489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d227799 q = 0) : d229595 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d227799, d229595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d227799, d229595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d227961 q = 0) : d229715 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d227961, d229715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d227961, d229715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22567 (p : Pattern) (selected : d227967 p = 0) : d229721 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227962 q = 0) : d229716 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d227962, d229716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22566 q selected
    | true =>
      simp only [d227962, d229716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22537 q selected
  have h2 (q : Pattern) (selected : d227963 q = 0) : d229717 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d227963, d229717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227963, d229717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227964 q = 0) : d229718 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d227964, d229718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227964, d229718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227801 q = 0) : d229597 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d227801, d229597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22537 q selected
    | true =>
      simp only [d227801, d229597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22520 q selected
  have h5 (q : Pattern) (selected : d227802 q = 0) : d229598 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d227802, d229598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227802, d229598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227803 q = 0) : d229599 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d227803, d229599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227803, d229599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d227965 q = 0) : d229719 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d227965, d229719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227965, d229719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d227696 q = 0) : d229492 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d227696, d229492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22520 q selected
    | true =>
      simp only [d227696, d229492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d227697 q = 0) : d229493 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d227697, d229493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227697, d229493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227698 q = 0) : d229494 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d227698, d229494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227698, d229494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d227804 q = 0) : d229600 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d227804, d229600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d227804, d229600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d227966 q = 0) : d229720 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d227966, d229720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227966, d229720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d227967 q = 0) : d229721 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d227967, d229721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d227967, d229721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro22568 (p : Pattern) (selected : d227973 p = 0) : d229727 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227968 q = 0) : d229722 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227968, d229722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22567 q selected
    | true =>
      simp only [d227968, d229722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227969 q = 0) : d229723 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227969, d229723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227969, d229723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227807 q = 0) : d229603 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227807, d229603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22538 q selected
    | true =>
      simp only [d227807, d229603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227808 q = 0) : d229604 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227808, d229604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227808, d229604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d227970 q = 0) : d229724 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d227970, d229724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227970, d229724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227971 q = 0) : d229725 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d227971, d229725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227971, d229725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d227972 q = 0) : d229726 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d227972, d229726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d227972, d229726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d227973 q = 0) : d229727 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d227973, d229727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227973, d229727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22569 (p : Pattern) (selected : d227976 p = 0) : d229590 p = 1 := by
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
  have h3 (q : Pattern) (selected : d164 q = 0) : d51871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
    | true =>
      simp only [d164, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d165 q = 0) : d51872 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d165, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d165, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d346 q = 0) : d51986 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d346, d51986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d346, d51986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227975 q = 0) : d229589 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d227975, d229589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227975, d229589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d166 q = 0) : d51873 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d166, d51873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166, d51873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d227814 q = 0) : d229484 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d227814, d229484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227814, d229484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d227976 q = 0) : d229590 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d227976, d229590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d227976, d229590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro22570 (p : Pattern) (selected : d227982 p = 0) : d229596 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227977 q = 0) : d229591 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227977, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22569 q selected
    | true =>
      simp only [d227977, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227978 q = 0) : d229592 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227978, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227978, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d227979 q = 0) : d229593 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227979, d229593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227979, d229593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227980 q = 0) : d229594 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227980, d229594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227980, d229594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227816 q = 0) : d229486 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227816, d229486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22540 q selected
    | true =>
      simp only [d227816, d229486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d227817 q = 0) : d229487 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227817, d229487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227817, d229487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d227818 q = 0) : d229488 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227818, d229488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227818, d229488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d227819 q = 0) : d229489 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227819, d229489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227819, d229489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d227981 q = 0) : d229595 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d227981, d229595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227981, d229595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227820 q = 0) : d229490 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d227820, d229490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d227820, d229490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d227982 q = 0) : d229596 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d227982, d229596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d227982, d229596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22571 (p : Pattern) (selected : d227988 p = 0) : d229602 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227983 q = 0) : d229597 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d227983, d229597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22570 q selected
    | true =>
      simp only [d227983, d229597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22541 q selected
  have h2 (q : Pattern) (selected : d227984 q = 0) : d229598 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d227984, d229598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227984, d229598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227985 q = 0) : d229599 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d227985, d229599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227985, d229599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227822 q = 0) : d229492 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d227822, d229492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22541 q selected
    | true =>
      simp only [d227822, d229492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227823 q = 0) : d229493 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d227823, d229493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227823, d229493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227824 q = 0) : d229494 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d227824, d229494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227824, d229494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d227986 q = 0) : d229600 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d227986, d229600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227986, d229600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d227825 q = 0) : d229495 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d227825, d229495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d227825, d229495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d227987 q = 0) : d229601 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d227987, d229601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227987, d229601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227988 q = 0) : d229602 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d227988, d229602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d227988, d229602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22572 (p : Pattern) (selected : d227994 p = 0) : d229608 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227989 q = 0) : d229603 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227989, d229603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22571 q selected
    | true =>
      simp only [d227989, d229603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227990 q = 0) : d229604 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227990, d229604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227990, d229604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227828 q = 0) : d229498 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227828, d229498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22542 q selected
    | true =>
      simp only [d227828, d229498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227829 q = 0) : d229499 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227829, d229499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227829, d229499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d227991 q = 0) : d229605 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d227991, d229605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227991, d229605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227992 q = 0) : d229606 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d227992, d229606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227992, d229606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d227993 q = 0) : d229607 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d227993, d229607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d227993, d229607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d227994 q = 0) : d229608 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d227994, d229608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227994, d229608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22573 (p : Pattern) (selected : d228000 p = 0) : d229733 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227807 q = 0) : d229603 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227807, d229603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22538 q selected
    | true =>
      simp only [d227807, d229603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227808 q = 0) : d229604 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227808, d229604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227808, d229604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227997 q = 0) : d229730 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d227997, d229730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227997, d229730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227998 q = 0) : d229731 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d227998, d229731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227998, d229731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227999 q = 0) : d229732 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d227999, d229732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227999, d229732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228000 q = 0) : d229733 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228000, d229733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228000, d229733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22574 (p : Pattern) (selected : d228006 p = 0) : d229739 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227944 q = 0) : d229698 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227944, d229698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22563 q selected
    | true =>
      simp only [d227944, d229698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22534 q selected
  have h2 (q : Pattern) (selected : d227945 q = 0) : d229699 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227945, d229699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227945, d229699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227946 q = 0) : d229700 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d227946, d229700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227946, d229700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227947 q = 0) : d229701 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d227947, d229701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227947, d229701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d227951 q = 0) : d229705 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227951, d229705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22564 q selected
    | true =>
      simp only [d227951, d229705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22535 q selected
  have h6 (q : Pattern) (selected : d227952 q = 0) : d229706 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227952, d229706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227952, d229706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d227953 q = 0) : d229707 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d227953, d229707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d227953, d229707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d227974 q = 0) : d229728 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227974, d229728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22568 q selected
    | true =>
      simp only [d227974, d229728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22539 q selected
  have h9 (q : Pattern) (selected : d227995 q = 0) : d229609 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227995, d229609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22572 q selected
    | true =>
      simp only [d227995, d229609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22543 q selected
  have h10 (q : Pattern) (selected : d227996 q = 0) : d229729 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227996, d229729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d227996, d229729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d228001 q = 0) : d229734 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228001, d229734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22573 q selected
    | true =>
      simp only [d228001, d229734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d228002 q = 0) : d229735 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228002, d229735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d228002, d229735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d228003 q = 0) : d229736 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228003, d229736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d228003, d229736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d228004 q = 0) : d229737 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228004, d229737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228004, d229737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d228005 q = 0) : d229738 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228005, d229738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228005, d229738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d228006 q = 0) : d229739 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228006, d229739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228006, d229739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro22575 (p : Pattern) (selected : d228007 p = 0) : d229740 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227807 q = 0) : d229603 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227807, d229603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22538 q selected
    | true =>
      simp only [d227807, d229603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227808 q = 0) : d229604 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227808, d229604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227808, d229604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227702 q = 0) : d229498 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227702, d229498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22521 q selected
    | true =>
      simp only [d227702, d229498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227703 q = 0) : d229499 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227703, d229499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227703, d229499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d227809 q = 0) : d229605 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d227809, d229605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227809, d229605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227810 q = 0) : d229606 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d227810, d229606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227810, d229606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d227942 q = 0) : d229696 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d227942, d229696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227942, d229696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228007 q = 0) : d229740 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228007, d229740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228007, d229740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22576 (p : Pattern) (selected : d228012 p = 0) : d229745 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227807 q = 0) : d229603 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227807, d229603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22538 q selected
    | true =>
      simp only [d227807, d229603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227808 q = 0) : d229604 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227808, d229604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227808, d229604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227702 q = 0) : d229498 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227702, d229498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22521 q selected
    | true =>
      simp only [d227702, d229498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227703 q = 0) : d229499 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227703, d229499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227703, d229499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d227809 q = 0) : d229605 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d227809, d229605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227809, d229605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227948 q = 0) : d229702 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d227948, d229702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227948, d229702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d227949 q = 0) : d229703 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d227949, d229703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d227949, d229703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228012 q = 0) : d229745 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228012, d229745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228012, d229745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22577 (p : Pattern) (selected : d228016 p = 0) : d229749 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227968 q = 0) : d229722 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227968, d229722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22567 q selected
    | true =>
      simp only [d227968, d229722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227969 q = 0) : d229723 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227969, d229723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227969, d229723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227807 q = 0) : d229603 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227807, d229603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22538 q selected
    | true =>
      simp only [d227807, d229603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227808 q = 0) : d229604 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227808, d229604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227808, d229604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d227970 q = 0) : d229724 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d227970, d229724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227970, d229724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227971 q = 0) : d229725 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d227971, d229725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227971, d229725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d227972 q = 0) : d229726 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d227972, d229726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d227972, d229726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228016 q = 0) : d229749 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228016, d229749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228016, d229749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22578 (p : Pattern) (selected : d228018 p = 0) : d229624 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227989 q = 0) : d229603 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227989, d229603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22571 q selected
    | true =>
      simp only [d227989, d229603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227990 q = 0) : d229604 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227990, d229604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227990, d229604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227828 q = 0) : d229498 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227828, d229498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22542 q selected
    | true =>
      simp only [d227828, d229498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227829 q = 0) : d229499 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227829, d229499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227829, d229499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d227991 q = 0) : d229605 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d227991, d229605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227991, d229605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227992 q = 0) : d229606 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d227992, d229606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227992, d229606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d227993 q = 0) : d229607 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d227993, d229607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d227993, d229607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228018 q = 0) : d229624 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228018, d229624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228018, d229624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22579 (p : Pattern) (selected : d228021 p = 0) : d229752 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227807 q = 0) : d229603 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227807, d229603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22538 q selected
    | true =>
      simp only [d227807, d229603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227808 q = 0) : d229604 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227808, d229604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227808, d229604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227997 q = 0) : d229730 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d227997, d229730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227997, d229730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227998 q = 0) : d229731 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d227998, d229731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227998, d229731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227999 q = 0) : d229732 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d227999, d229732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227999, d229732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228021 q = 0) : d229752 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228021, d229752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228021, d229752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22580 (p : Pattern) (selected : d228027 p = 0) : d229758 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227944 q = 0) : d229698 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227944, d229698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22563 q selected
    | true =>
      simp only [d227944, d229698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22534 q selected
  have h2 (q : Pattern) (selected : d227945 q = 0) : d229699 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227945, d229699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227945, d229699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227946 q = 0) : d229700 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d227946, d229700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227946, d229700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227947 q = 0) : d229701 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d227947, d229701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227947, d229701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d227951 q = 0) : d229705 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227951, d229705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22564 q selected
    | true =>
      simp only [d227951, d229705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22535 q selected
  have h6 (q : Pattern) (selected : d227952 q = 0) : d229706 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227952, d229706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227952, d229706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d227953 q = 0) : d229707 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d227953, d229707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d227953, d229707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d227974 q = 0) : d229728 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227974, d229728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22568 q selected
    | true =>
      simp only [d227974, d229728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22539 q selected
  have h9 (q : Pattern) (selected : d227995 q = 0) : d229609 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227995, d229609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22572 q selected
    | true =>
      simp only [d227995, d229609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22543 q selected
  have h10 (q : Pattern) (selected : d227996 q = 0) : d229729 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227996, d229729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d227996, d229729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d228001 q = 0) : d229734 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228001, d229734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22573 q selected
    | true =>
      simp only [d228001, d229734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d228002 q = 0) : d229735 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228002, d229735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d228002, d229735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d228003 q = 0) : d229736 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228003, d229736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d228003, d229736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d228004 q = 0) : d229737 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228004, d229737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228004, d229737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d228005 q = 0) : d229738 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228005, d229738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228005, d229738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d228008 q = 0) : d229741 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228008, d229741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22575 q selected
    | true =>
      simp only [d228008, d229741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22545 q selected
  have h17 (q : Pattern) (selected : d228009 q = 0) : d229742 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228009, d229742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228009, d229742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d228010 q = 0) : d229743 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228010, d229743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d228010, d229743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d228011 q = 0) : d229744 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228011, d229744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228011, d229744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d228013 q = 0) : d229746 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228013, d229746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22576 q selected
    | true =>
      simp only [d228013, d229746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22546 q selected
  have h21 (q : Pattern) (selected : d228014 q = 0) : d229747 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228014, d229747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228014, d229747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d228015 q = 0) : d229748 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228015, d229748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d228015, d229748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d228017 q = 0) : d229750 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228017, d229750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22577 q selected
    | true =>
      simp only [d228017, d229750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22547 q selected
  have h24 (q : Pattern) (selected : d228019 q = 0) : d229625 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228019, d229625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22578 q selected
    | true =>
      simp only [d228019, d229625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22548 q selected
  have h25 (q : Pattern) (selected : d228020 q = 0) : d229751 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228020, d229751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d228020, d229751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d228022 q = 0) : d229753 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228022, d229753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22579 q selected
    | true =>
      simp only [d228022, d229753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d228023 q = 0) : d229754 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228023, d229754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d228023, d229754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d228024 q = 0) : d229755 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228024, d229755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d228024, d229755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d228025 q = 0) : d229756 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228025, d229756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d228025, d229756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d228026 q = 0) : d229757 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228026, d229757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d228026, d229757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d228027 q = 0) : d229758 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228027, d229758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d228027, d229758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro22581 (p : Pattern) (selected : d228029 p = 0) : d229760 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227813 q = 0) : d229609 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227813, d229609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22539 q selected
    | true =>
      simp only [d227813, d229609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22522 q selected
  have h2 (q : Pattern) (selected : d227927 q = 0) : d229681 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227927, d229681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227927, d229681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227928 q = 0) : d229682 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d227928, d229682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227928, d229682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227929 q = 0) : d229683 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d227929, d229683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227929, d229683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d227930 q = 0) : d229684 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d227930, d229684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227930, d229684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227708 q = 0) : d229504 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227708, d229504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22522 q selected
    | true =>
      simp only [d227708, d229504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d227766 q = 0) : d229562 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227766, d229562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227766, d229562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d227767 q = 0) : d229563 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d227767, d229563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227767, d229563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d227768 q = 0) : d229564 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d227768, d229564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227768, d229564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227769 q = 0) : d229565 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d227769, d229565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227769, d229565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d228029 q = 0) : d229760 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228029, d229760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228029, d229760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22582 (p : Pattern) (selected : d228036 p = 0) : d229767 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228017 q = 0) : d229750 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228017, d229750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22577 q selected
    | true =>
      simp only [d228017, d229750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22547 q selected
  have h2 (q : Pattern) (selected : d228019 q = 0) : d229625 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228019, d229625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22578 q selected
    | true =>
      simp only [d228019, d229625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22548 q selected
  have h3 (q : Pattern) (selected : d228020 q = 0) : d229751 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228020, d229751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228020, d229751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228022 q = 0) : d229753 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228022, d229753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22579 q selected
    | true =>
      simp only [d228022, d229753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228023 q = 0) : d229754 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228023, d229754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228023, d229754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228024 q = 0) : d229755 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228024, d229755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228024, d229755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228034 q = 0) : d229765 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228034, d229765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228034, d229765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228035 q = 0) : d229766 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228035, d229766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228035, d229766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d228036 q = 0) : d229767 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228036, d229767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228036, d229767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro22583 (p : Pattern) (selected : d228038 p = 0) : d229769 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227715 q = 0) : d229511 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227715, d229511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22524 q selected
    | true =>
      simp only [d227715, d229511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227773 q = 0) : d229569 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d227773, d229569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227773, d229569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227774 q = 0) : d229570 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d227774, d229570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227774, d229570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227775 q = 0) : d229571 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d227775, d229571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227775, d229571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d227776 q = 0) : d229572 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d227776, d229572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227776, d229572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228038 q = 0) : d229769 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228038, d229769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228038, d229769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22584 (p : Pattern) (selected : d228049 p = 0) : d229780 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228044 q = 0) : d229775 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228044, d229775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228044, d229775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22565 q selected
  have h2 (q : Pattern) (selected : d227956 q = 0) : d229710 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227956, d229710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22565 q selected
    | true =>
      simp only [d227956, d229710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228045 q = 0) : d229776 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228045, d229776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228045, d229776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227957 q = 0) : d229711 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227957, d229711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227957, d229711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228046 q = 0) : d229777 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228046, d229777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228046, d229777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228047 q = 0) : d229778 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228047, d229778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228047, d229778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d227872 q = 0) : d229645 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227872, d229645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227872, d229645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22536 q selected
  have h8 (q : Pattern) (selected : d227795 q = 0) : d229591 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227795, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22536 q selected
    | true =>
      simp only [d227795, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d227873 q = 0) : d229646 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227873, d229646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227873, d229646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227796 q = 0) : d229592 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227796, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d227796, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d227874 q = 0) : d229647 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227874, d229647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d227874, d229647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d227875 q = 0) : d229648 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227875, d229648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d227875, d229648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d228048 q = 0) : d229779 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228048, d229779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228048, d229779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d227731 q = 0) : d229527 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227731, d229527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227731, d229527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22519 q selected
  have h15 (q : Pattern) (selected : d227690 q = 0) : d229486 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227690, d229486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22519 q selected
    | true =>
      simp only [d227690, d229486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d227732 q = 0) : d229528 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227732, d229528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d227732, d229528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d227691 q = 0) : d229487 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227691, d229487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d227691, d229487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d227733 q = 0) : d229529 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227733, d229529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d227733, d229529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d227734 q = 0) : d229530 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227734, d229530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d227734, d229530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d227876 q = 0) : d229649 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d227876, d229649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d227876, d229649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d228049 q = 0) : d229780 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228049, d229780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d228049, d229780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro22585 (p : Pattern) (selected : d228055 p = 0) : d229786 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228050 q = 0) : d229781 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228050, d229781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22584 q selected
    | true =>
      simp only [d228050, d229781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22552 q selected
  have h2 (q : Pattern) (selected : d228051 q = 0) : d229782 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228051, d229782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228051, d229782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228052 q = 0) : d229783 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228052, d229783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228052, d229783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227878 q = 0) : d229651 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d227878, d229651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22552 q selected
    | true =>
      simp only [d227878, d229651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22527 q selected
  have h5 (q : Pattern) (selected : d227879 q = 0) : d229652 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d227879, d229652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227879, d229652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227880 q = 0) : d229653 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d227880, d229653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227880, d229653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228053 q = 0) : d229784 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228053, d229784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228053, d229784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d227737 q = 0) : d229533 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d227737, d229533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22527 q selected
    | true =>
      simp only [d227737, d229533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d227738 q = 0) : d229534 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d227738, d229534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227738, d229534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227739 q = 0) : d229535 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d227739, d229535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227739, d229535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d227881 q = 0) : d229654 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d227881, d229654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d227881, d229654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d228054 q = 0) : d229785 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228054, d229785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228054, d229785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d228055 q = 0) : d229786 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228055, d229786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d228055, d229786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro22586 (p : Pattern) (selected : d228061 p = 0) : d229792 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228056 q = 0) : d229787 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228056, d229787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22585 q selected
    | true =>
      simp only [d228056, d229787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228057 q = 0) : d229788 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228057, d229788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228057, d229788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227884 q = 0) : d229657 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227884, d229657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22553 q selected
    | true =>
      simp only [d227884, d229657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227885 q = 0) : d229658 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227885, d229658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227885, d229658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228058 q = 0) : d229789 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228058, d229789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228058, d229789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228059 q = 0) : d229790 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228059, d229790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228059, d229790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228060 q = 0) : d229791 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228060, d229791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228060, d229791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228061 q = 0) : d229792 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228061, d229792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228061, d229792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22587 (p : Pattern) (selected : d228068 p = 0) : d229650 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228063 q = 0) : d229645 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228063, d229645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228063, d229645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22569 q selected
  have h2 (q : Pattern) (selected : d227977 q = 0) : d229591 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227977, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22569 q selected
    | true =>
      simp only [d227977, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228064 q = 0) : d229646 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228064, d229646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228064, d229646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227978 q = 0) : d229592 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227978, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227978, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228065 q = 0) : d229647 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228065, d229647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228065, d229647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228066 q = 0) : d229648 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228066, d229648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228066, d229648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d227891 q = 0) : d229527 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227891, d229527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227891, d229527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22540 q selected
  have h8 (q : Pattern) (selected : d227816 q = 0) : d229486 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227816, d229486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22540 q selected
    | true =>
      simp only [d227816, d229486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d227892 q = 0) : d229528 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227892, d229528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227892, d229528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227817 q = 0) : d229487 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227817, d229487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d227817, d229487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d227893 q = 0) : d229529 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227893, d229529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d227893, d229529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d227894 q = 0) : d229530 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227894, d229530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d227894, d229530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d228067 q = 0) : d229649 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228067, d229649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228067, d229649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d227895 q = 0) : d229531 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d227895, d229531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d227895, d229531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d228068 q = 0) : d229650 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228068, d229650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d228068, d229650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22588 (p : Pattern) (selected : d228074 p = 0) : d229656 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228069 q = 0) : d229651 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228069, d229651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22587 q selected
    | true =>
      simp only [d228069, d229651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22555 q selected
  have h2 (q : Pattern) (selected : d228070 q = 0) : d229652 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228070, d229652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228070, d229652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228071 q = 0) : d229653 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228071, d229653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228071, d229653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227897 q = 0) : d229533 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d227897, d229533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22555 q selected
    | true =>
      simp only [d227897, d229533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227898 q = 0) : d229534 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d227898, d229534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227898, d229534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227899 q = 0) : d229535 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d227899, d229535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227899, d229535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228072 q = 0) : d229654 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228072, d229654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228072, d229654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d227900 q = 0) : d229536 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d227900, d229536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d227900, d229536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228073 q = 0) : d229655 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228073, d229655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228073, d229655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228074 q = 0) : d229656 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228074, d229656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228074, d229656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22589 (p : Pattern) (selected : d228080 p = 0) : d229662 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228075 q = 0) : d229657 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228075, d229657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22588 q selected
    | true =>
      simp only [d228075, d229657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228076 q = 0) : d229658 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228076, d229658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228076, d229658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227903 q = 0) : d229539 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227903, d229539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22556 q selected
    | true =>
      simp only [d227903, d229539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d227904 q = 0) : d229540 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227904, d229540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227904, d229540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228077 q = 0) : d229659 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228077, d229659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228077, d229659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228078 q = 0) : d229660 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228078, d229660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228078, d229660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228079 q = 0) : d229661 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228079, d229661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228079, d229661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228080 q = 0) : d229662 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228080, d229662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228080, d229662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22590 (p : Pattern) (selected : d228086 p = 0) : d229798 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227884 q = 0) : d229657 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d227884, d229657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22553 q selected
    | true =>
      simp only [d227884, d229657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227885 q = 0) : d229658 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d227885, d229658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227885, d229658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228083 q = 0) : d229795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228083, d229795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228083, d229795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228084 q = 0) : d229796 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228084, d229796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228084, d229796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228085 q = 0) : d229797 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228085, d229797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228085, d229797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228086 q = 0) : d229798 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228086, d229798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228086, d229798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22591 (p : Pattern) (selected : d228092 p = 0) : d229804 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228062 q = 0) : d229793 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228062, d229793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22586 q selected
    | true =>
      simp only [d228062, d229793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22554 q selected
  have h2 (q : Pattern) (selected : d228081 q = 0) : d229663 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228081, d229663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22589 q selected
    | true =>
      simp only [d228081, d229663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22557 q selected
  have h3 (q : Pattern) (selected : d228082 q = 0) : d229794 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228082, d229794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228082, d229794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228087 q = 0) : d229799 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228087, d229799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22590 q selected
    | true =>
      simp only [d228087, d229799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228088 q = 0) : d229800 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228088, d229800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228088, d229800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228089 q = 0) : d229801 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228089, d229801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228089, d229801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228090 q = 0) : d229802 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228090, d229802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228090, d229802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228091 q = 0) : d229803 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228091, d229803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228091, d229803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d228092 q = 0) : d229804 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228092, d229804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228092, d229804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro22592 (p : Pattern) (selected : d228098 p = 0) : d229810 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227749 q = 0) : d229545 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d227749, d229545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22529 q selected
    | true =>
      simp only [d227749, d229545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228094 q = 0) : d229806 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228094, d229806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228094, d229806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228095 q = 0) : d229807 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228095, d229807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228095, d229807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228096 q = 0) : d229808 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228096, d229808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228096, d229808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228097 q = 0) : d229809 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228097, d229809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228097, d229809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228098 q = 0) : d229810 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228098, d229810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228098, d229810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22593 (p : Pattern) (selected : d228104 p = 0) : d229816 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227932 q = 0) : d229686 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d227932, d229686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227932, d229686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22561 q selected
  have h2 (q : Pattern) (selected : d227933 q = 0) : d229687 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d227933, d229687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227933, d229687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d227939 q = 0) : d229693 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d227939, d229693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22561 q selected
    | true =>
      simp only [d227939, d229693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22562 q selected
  have h4 (q : Pattern) (selected : d227940 q = 0) : d229694 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d227940, d229694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227940, d229694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227941 q = 0) : d229695 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d227941, d229695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227941, d229695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228028 q = 0) : d229759 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228028, d229759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22574 q selected
    | true =>
      simp only [d228028, d229759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22580 q selected
  have h7 (q : Pattern) (selected : d228030 q = 0) : d229761 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228030, d229761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22581 q selected
    | true =>
      simp only [d228030, d229761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22533 q selected
  have h8 (q : Pattern) (selected : d228031 q = 0) : d229762 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d228031, d229762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228031, d229762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d228032 q = 0) : d229763 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d228032, d229763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d228032, d229763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d228033 q = 0) : d229764 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d228033, d229764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228033, d229764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d228037 q = 0) : d229768 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228037, d229768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228037, d229768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22582 q selected
  have h12 (q : Pattern) (selected : d228039 q = 0) : d229770 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228039, d229770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228039, d229770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22583 q selected
  have h13 (q : Pattern) (selected : d228040 q = 0) : d229771 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d228040, d229771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d228040, d229771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d228041 q = 0) : d229772 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d228041, d229772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d228041, d229772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d228042 q = 0) : d229773 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d228042, d229773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d228042, d229773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d228043 q = 0) : d229774 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d228043, d229774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d228043, d229774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d228093 q = 0) : d229805 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228093, d229805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228093, d229805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22591 q selected
  have h18 (q : Pattern) (selected : d228099 q = 0) : d229811 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228099, d229811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228099, d229811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22592 q selected
  have h19 (q : Pattern) (selected : d228100 q = 0) : d229812 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d228100, d229812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d228100, d229812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d228101 q = 0) : d229813 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d228101, d229813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d228101, d229813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d228102 q = 0) : d229814 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d228102, d229814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d228102, d229814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d228103 q = 0) : d229815 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d228103, d229815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d228103, d229815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d228104 q = 0) : d229816 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d228104, d229816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d228104, d229816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro22594 (p : Pattern) (selected : d228110 p = 0) : d229822 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228105 q = 0) : d229817 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d228105, d229817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228105, d229817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22593 q selected
  have h2 (q : Pattern) (selected : d228106 q = 0) : d229818 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d228106, d229818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228106, d229818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228107 q = 0) : d229819 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d228107, d229819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228107, d229819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228108 q = 0) : d229820 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d228108, d229820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228108, d229820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228109 q = 0) : d229821 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d228109, d229821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228109, d229821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228110 q = 0) : d229822 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d228110, d229822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228110, d229822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22595 (p : Pattern) (selected : d228114 p = 0) : d229826 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227962 q = 0) : d229716 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d227962, d229716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22566 q selected
    | true =>
      simp only [d227962, d229716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22537 q selected
  have h2 (q : Pattern) (selected : d227963 q = 0) : d229717 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d227963, d229717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227963, d229717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227964 q = 0) : d229718 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d227964, d229718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227964, d229718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227801 q = 0) : d229597 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d227801, d229597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22537 q selected
    | true =>
      simp only [d227801, d229597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22520 q selected
  have h5 (q : Pattern) (selected : d227802 q = 0) : d229598 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d227802, d229598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227802, d229598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227803 q = 0) : d229599 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d227803, d229599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227803, d229599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d227965 q = 0) : d229719 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d227965, d229719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227965, d229719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228112 q = 0) : d229824 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228112, d229824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228112, d229824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228113 q = 0) : d229825 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228113, d229825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228113, d229825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228114 q = 0) : d229826 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228114, d229826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228114, d229826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22596 (p : Pattern) (selected : d228118 p = 0) : d229830 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227801 q = 0) : d229597 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d227801, d229597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22537 q selected
    | true =>
      simp only [d227801, d229597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22520 q selected
  have h2 (q : Pattern) (selected : d227802 q = 0) : d229598 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d227802, d229598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227802, d229598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227803 q = 0) : d229599 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d227803, d229599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227803, d229599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228112 q = 0) : d229824 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228112, d229824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228112, d229824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228117 q = 0) : d229829 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228117, d229829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228117, d229829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228118 q = 0) : d229830 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228118, d229830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228118, d229830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22597 (p : Pattern) (selected : d228124 p = 0) : d229836 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228115 q = 0) : d229827 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228115, d229827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22595 q selected
    | true =>
      simp only [d228115, d229827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228116 q = 0) : d229828 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228116, d229828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228116, d229828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228119 q = 0) : d229831 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228119, d229831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22596 q selected
    | true =>
      simp only [d228119, d229831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228120 q = 0) : d229832 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228120, d229832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228120, d229832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228121 q = 0) : d229833 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228121, d229833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228121, d229833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228122 q = 0) : d229834 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228122, d229834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228122, d229834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228123 q = 0) : d229835 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228123, d229835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228123, d229835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228124 q = 0) : d229836 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228124, d229836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228124, d229836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22598 (p : Pattern) (selected : d228128 p = 0) : d229840 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228119 q = 0) : d229831 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228119, d229831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22596 q selected
    | true =>
      simp only [d228119, d229831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228120 q = 0) : d229832 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228120, d229832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228120, d229832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228125 q = 0) : d229837 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228125, d229837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228125, d229837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228126 q = 0) : d229838 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228126, d229838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228126, d229838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228127 q = 0) : d229839 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228127, d229839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228127, d229839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228128 q = 0) : d229840 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228128, d229840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228128, d229840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22599 (p : Pattern) (selected : d228134 p = 0) : d229846 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228129 q = 0) : d229841 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228129, d229841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22597 q selected
    | true =>
      simp only [d228129, d229841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22598 q selected
  have h2 (q : Pattern) (selected : d228130 q = 0) : d229842 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228130, d229842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228130, d229842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228131 q = 0) : d229843 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228131, d229843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228131, d229843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228132 q = 0) : d229844 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228132, d229844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228132, d229844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228133 q = 0) : d229845 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228133, d229845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228133, d229845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228134 q = 0) : d229846 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228134, d229846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228134, d229846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22600 (p : Pattern) (selected : d228137 p = 0) : d229849 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228115 q = 0) : d229827 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228115, d229827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22595 q selected
    | true =>
      simp only [d228115, d229827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228116 q = 0) : d229828 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228116, d229828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228116, d229828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228119 q = 0) : d229831 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228119, d229831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22596 q selected
    | true =>
      simp only [d228119, d229831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228120 q = 0) : d229832 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228120, d229832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228120, d229832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228121 q = 0) : d229833 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228121, d229833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228121, d229833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228122 q = 0) : d229834 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228122, d229834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228122, d229834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228123 q = 0) : d229835 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228123, d229835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228123, d229835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228137 q = 0) : d229849 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228137, d229849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228137, d229849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22601 (p : Pattern) (selected : d228138 p = 0) : d229850 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228119 q = 0) : d229831 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228119, d229831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22596 q selected
    | true =>
      simp only [d228119, d229831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228120 q = 0) : d229832 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228120, d229832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228120, d229832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228125 q = 0) : d229837 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228125, d229837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228125, d229837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228126 q = 0) : d229838 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228126, d229838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228126, d229838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228127 q = 0) : d229839 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228127, d229839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228127, d229839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228138 q = 0) : d229850 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228138, d229850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228138, d229850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22602 (p : Pattern) (selected : d228144 p = 0) : d229856 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228129 q = 0) : d229841 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228129, d229841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22597 q selected
    | true =>
      simp only [d228129, d229841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22598 q selected
  have h2 (q : Pattern) (selected : d228130 q = 0) : d229842 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228130, d229842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228130, d229842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228131 q = 0) : d229843 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228131, d229843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228131, d229843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228132 q = 0) : d229844 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228132, d229844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228132, d229844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228133 q = 0) : d229845 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228133, d229845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228133, d229845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228139 q = 0) : d229851 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228139, d229851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22600 q selected
    | true =>
      simp only [d228139, d229851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22601 q selected
  have h7 (q : Pattern) (selected : d228140 q = 0) : d229852 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228140, d229852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228140, d229852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228141 q = 0) : d229853 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228141, d229853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228141, d229853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228142 q = 0) : d229854 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228142, d229854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228142, d229854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228143 q = 0) : d229855 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228143, d229855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228143, d229855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d228144 q = 0) : d229856 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228144, d229856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228144, d229856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22603 (p : Pattern) (selected : d228149 p = 0) : d229861 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228115 q = 0) : d229827 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228115, d229827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22595 q selected
    | true =>
      simp only [d228115, d229827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228116 q = 0) : d229828 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228116, d229828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228116, d229828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228119 q = 0) : d229831 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228119, d229831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22596 q selected
    | true =>
      simp only [d228119, d229831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228120 q = 0) : d229832 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228120, d229832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228120, d229832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228121 q = 0) : d229833 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228121, d229833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228121, d229833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228122 q = 0) : d229834 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228122, d229834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228122, d229834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228148 q = 0) : d229860 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228148, d229860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228148, d229860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228149 q = 0) : d229861 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228149, d229861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228149, d229861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22604 (p : Pattern) (selected : d228151 p = 0) : d229863 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228119 q = 0) : d229831 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228119, d229831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22596 q selected
    | true =>
      simp only [d228119, d229831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228120 q = 0) : d229832 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228120, d229832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228120, d229832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228125 q = 0) : d229837 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228125, d229837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228125, d229837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228126 q = 0) : d229838 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228126, d229838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228126, d229838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228150 q = 0) : d229862 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228150, d229862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228150, d229862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228151 q = 0) : d229863 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228151, d229863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228151, d229863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22605 (p : Pattern) (selected : d228158 p = 0) : d229870 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228115 q = 0) : d229827 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228115, d229827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22595 q selected
    | true =>
      simp only [d228115, d229827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228116 q = 0) : d229828 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228116, d229828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228116, d229828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228119 q = 0) : d229831 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228119, d229831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22596 q selected
    | true =>
      simp only [d228119, d229831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228120 q = 0) : d229832 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228120, d229832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228120, d229832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228121 q = 0) : d229833 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228121, d229833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228121, d229833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228156 q = 0) : d229868 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228156, d229868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228156, d229868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228157 q = 0) : d229869 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228157, d229869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228157, d229869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228158 q = 0) : d229870 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228158, d229870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228158, d229870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22606 (p : Pattern) (selected : d228161 p = 0) : d229873 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228119 q = 0) : d229831 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228119, d229831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22596 q selected
    | true =>
      simp only [d228119, d229831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228120 q = 0) : d229832 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228120, d229832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228120, d229832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228125 q = 0) : d229837 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228125, d229837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228125, d229837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228159 q = 0) : d229871 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228159, d229871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228159, d229871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228160 q = 0) : d229872 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228160, d229872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228160, d229872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228161 q = 0) : d229873 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228161, d229873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228161, d229873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22607 (p : Pattern) (selected : d228166 p = 0) : d229878 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d828 q = 0) : d52505 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d828, d52505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro334 q selected
    | true =>
      simp only [d828, d52505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d829 q = 0) : d52506 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d829, d52506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d829, d52506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d537 q = 0) : d52284 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d537, d52284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro276 q selected
    | true =>
      simp only [d537, d52284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d538 q = 0) : d52285 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d538, d52285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d538, d52285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d830 q = 0) : d52507 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d830, d52507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d830, d52507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228165 q = 0) : d229877 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d228165, d229877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228165, d229877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133 q = 0) : d51984 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro204 q selected
    | true =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d134 q = 0) : d51985 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d539 q = 0) : d52286 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d539, d52286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d539, d52286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227954 q = 0) : d229708 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d227954, d229708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d227954, d229708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d228166 q = 0) : d229878 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d228166, d229878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228166, d229878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22608 (p : Pattern) (selected : d228172 p = 0) : d229884 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228167 q = 0) : d229879 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228167, d229879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22607 q selected
    | true =>
      simp only [d228167, d229879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228168 q = 0) : d229880 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228168, d229880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228168, d229880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228169 q = 0) : d229881 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228169, d229881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228169, d229881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228170 q = 0) : d229882 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228170, d229882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228170, d229882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227956 q = 0) : d229710 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227956, d229710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22565 q selected
    | true =>
      simp only [d227956, d229710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d227957 q = 0) : d229711 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227957, d229711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227957, d229711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d227958 q = 0) : d229712 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227958, d229712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227958, d229712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d227959 q = 0) : d229713 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227959, d229713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227959, d229713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228171 q = 0) : d229883 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228171, d229883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228171, d229883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227795 q = 0) : d229591 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227795, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22536 q selected
    | true =>
      simp only [d227795, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d227796 q = 0) : d229592 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227796, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d227796, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d227797 q = 0) : d229593 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227797, d229593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227797, d229593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d227798 q = 0) : d229594 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227798, d229594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d227798, d229594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d227960 q = 0) : d229714 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d227960, d229714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d227960, d229714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d228172 q = 0) : d229884 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228172, d229884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228172, d229884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22609 (p : Pattern) (selected : d228178 p = 0) : d229890 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228173 q = 0) : d229885 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228173, d229885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22608 q selected
    | true =>
      simp only [d228173, d229885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22566 q selected
  have h2 (q : Pattern) (selected : d228174 q = 0) : d229886 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228174, d229886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228174, d229886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228175 q = 0) : d229887 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228175, d229887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228175, d229887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227962 q = 0) : d229716 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d227962, d229716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22566 q selected
    | true =>
      simp only [d227962, d229716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22537 q selected
  have h5 (q : Pattern) (selected : d227963 q = 0) : d229717 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d227963, d229717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227963, d229717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227964 q = 0) : d229718 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d227964, d229718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227964, d229718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228176 q = 0) : d229888 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228176, d229888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228176, d229888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d227801 q = 0) : d229597 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d227801, d229597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22537 q selected
    | true =>
      simp only [d227801, d229597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22520 q selected
  have h9 (q : Pattern) (selected : d227802 q = 0) : d229598 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d227802, d229598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227802, d229598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227803 q = 0) : d229599 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d227803, d229599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227803, d229599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d227965 q = 0) : d229719 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d227965, d229719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d227965, d229719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d228177 q = 0) : d229889 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228177, d229889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228177, d229889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d228178 q = 0) : d229890 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228178, d229890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d228178, d229890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro22610 (p : Pattern) (selected : d228184 p = 0) : d229896 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228179 q = 0) : d229891 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228179, d229891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22609 q selected
    | true =>
      simp only [d228179, d229891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228180 q = 0) : d229892 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228180, d229892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228180, d229892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228115 q = 0) : d229827 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228115, d229827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22595 q selected
    | true =>
      simp only [d228115, d229827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228116 q = 0) : d229828 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228116, d229828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228116, d229828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228181 q = 0) : d229893 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228181, d229893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228181, d229893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228182 q = 0) : d229894 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228182, d229894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228182, d229894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228183 q = 0) : d229895 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228183, d229895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228183, d229895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228184 q = 0) : d229896 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228184, d229896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228184, d229896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22611 (p : Pattern) (selected : d228187 p = 0) : d229709 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d862 q = 0) : d52284 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d862, d52284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro340 q selected
    | true =>
      simp only [d862, d52284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d863 q = 0) : d52285 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d863, d52285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d863, d52285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d344 q = 0) : d51984 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d344, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro239 q selected
    | true =>
      simp only [d344, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d345 q = 0) : d51985 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d345, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d345, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d864 q = 0) : d52286 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d864, d52286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d864, d52286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228186 q = 0) : d229708 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d228186, d229708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228186, d229708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d164 q = 0) : d51871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
    | true =>
      simp only [d164, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d165 q = 0) : d51872 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d165, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d165, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d346 q = 0) : d51986 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d346, d51986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d346, d51986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227975 q = 0) : d229589 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d227975, d229589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d227975, d229589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d228187 q = 0) : d229709 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d228187, d229709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228187, d229709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22612 (p : Pattern) (selected : d228193 p = 0) : d229715 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228188 q = 0) : d229710 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228188, d229710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22611 q selected
    | true =>
      simp only [d228188, d229710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228189 q = 0) : d229711 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228189, d229711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228189, d229711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228190 q = 0) : d229712 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228190, d229712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228190, d229712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228191 q = 0) : d229713 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228191, d229713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228191, d229713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227977 q = 0) : d229591 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227977, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22569 q selected
    | true =>
      simp only [d227977, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d227978 q = 0) : d229592 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227978, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227978, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d227979 q = 0) : d229593 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227979, d229593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227979, d229593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d227980 q = 0) : d229594 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227980, d229594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227980, d229594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228192 q = 0) : d229714 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228192, d229714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228192, d229714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227816 q = 0) : d229486 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227816, d229486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22540 q selected
    | true =>
      simp only [d227816, d229486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d227817 q = 0) : d229487 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227817, d229487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d227817, d229487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d227818 q = 0) : d229488 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227818, d229488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227818, d229488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d227819 q = 0) : d229489 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227819, d229489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d227819, d229489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d227981 q = 0) : d229595 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d227981, d229595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d227981, d229595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d228193 q = 0) : d229715 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228193, d229715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228193, d229715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22613 (p : Pattern) (selected : d228200 p = 0) : d229826 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228194 q = 0) : d229716 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228194, d229716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22612 q selected
    | true =>
      simp only [d228194, d229716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22570 q selected
  have h2 (q : Pattern) (selected : d228195 q = 0) : d229717 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228195, d229717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228195, d229717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228196 q = 0) : d229718 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228196, d229718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228196, d229718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227983 q = 0) : d229597 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d227983, d229597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22570 q selected
    | true =>
      simp only [d227983, d229597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22541 q selected
  have h5 (q : Pattern) (selected : d227984 q = 0) : d229598 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d227984, d229598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227984, d229598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227985 q = 0) : d229599 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d227985, d229599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227985, d229599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228197 q = 0) : d229719 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228197, d229719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228197, d229719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228198 q = 0) : d229824 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228198, d229824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228198, d229824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228199 q = 0) : d229825 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228199, d229825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228199, d229825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228200 q = 0) : d229826 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228200, d229826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228200, d229826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22614 (p : Pattern) (selected : d228204 p = 0) : d229830 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227983 q = 0) : d229597 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d227983, d229597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22570 q selected
    | true =>
      simp only [d227983, d229597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22541 q selected
  have h2 (q : Pattern) (selected : d227984 q = 0) : d229598 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d227984, d229598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227984, d229598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227985 q = 0) : d229599 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d227985, d229599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227985, d229599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228198 q = 0) : d229824 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228198, d229824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228198, d229824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228203 q = 0) : d229829 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228203, d229829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228203, d229829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228204 q = 0) : d229830 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228204, d229830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228204, d229830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22615 (p : Pattern) (selected : d228210 p = 0) : d229836 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228201 q = 0) : d229827 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228201, d229827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22613 q selected
    | true =>
      simp only [d228201, d229827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228202 q = 0) : d229828 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228202, d229828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228202, d229828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228205 q = 0) : d229831 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228205, d229831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22614 q selected
    | true =>
      simp only [d228205, d229831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228206 q = 0) : d229832 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228206, d229832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228206, d229832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228207 q = 0) : d229833 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228207, d229833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228207, d229833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228208 q = 0) : d229834 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228208, d229834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228208, d229834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228209 q = 0) : d229835 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228209, d229835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228209, d229835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228210 q = 0) : d229836 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228210, d229836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228210, d229836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22616 (p : Pattern) (selected : d228214 p = 0) : d229840 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228205 q = 0) : d229831 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228205, d229831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22614 q selected
    | true =>
      simp only [d228205, d229831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228206 q = 0) : d229832 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228206, d229832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228206, d229832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228211 q = 0) : d229837 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228211, d229837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228211, d229837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228212 q = 0) : d229838 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228212, d229838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228212, d229838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228213 q = 0) : d229839 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228213, d229839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228213, d229839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228214 q = 0) : d229840 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228214, d229840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228214, d229840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22617 (p : Pattern) (selected : d228217 p = 0) : d229899 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227795 q = 0) : d229591 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227795, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22536 q selected
    | true =>
      simp only [d227795, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227796 q = 0) : d229592 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227796, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227796, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d227797 q = 0) : d229593 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227797, d229593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227797, d229593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227798 q = 0) : d229594 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227798, d229594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227798, d229594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227690 q = 0) : d229486 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227690, d229486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22519 q selected
    | true =>
      simp only [d227690, d229486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d227691 q = 0) : d229487 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227691, d229487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227691, d229487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d227692 q = 0) : d229488 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227692, d229488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227692, d229488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d227693 q = 0) : d229489 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227693, d229489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227693, d229489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d227799 q = 0) : d229595 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d227799, d229595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227799, d229595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228217 q = 0) : d229899 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228217, d229899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228217, d229899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22618 (p : Pattern) (selected : d228223 p = 0) : d229905 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227962 q = 0) : d229716 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d227962, d229716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22566 q selected
    | true =>
      simp only [d227962, d229716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22537 q selected
  have h2 (q : Pattern) (selected : d227963 q = 0) : d229717 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d227963, d229717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227963, d229717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227964 q = 0) : d229718 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d227964, d229718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227964, d229718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227801 q = 0) : d229597 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d227801, d229597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22537 q selected
    | true =>
      simp only [d227801, d229597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22520 q selected
  have h5 (q : Pattern) (selected : d227802 q = 0) : d229598 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d227802, d229598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227802, d229598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227803 q = 0) : d229599 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d227803, d229599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227803, d229599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d227965 q = 0) : d229719 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d227965, d229719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227965, d229719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228218 q = 0) : d229900 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228218, d229900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22617 q selected
    | true =>
      simp only [d228218, d229900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228219 q = 0) : d229901 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228219, d229901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228219, d229901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228220 q = 0) : d229902 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228220, d229902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228220, d229902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d228221 q = 0) : d229903 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228221, d229903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d228221, d229903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d228222 q = 0) : d229904 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228222, d229904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228222, d229904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d228223 q = 0) : d229905 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228223, d229905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d228223, d229905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro22619 (p : Pattern) (selected : d228229 p = 0) : d229911 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228224 q = 0) : d229906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228224, d229906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22618 q selected
    | true =>
      simp only [d228224, d229906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228225 q = 0) : d229907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228225, d229907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228225, d229907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228226 q = 0) : d229908 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228226, d229908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228226, d229908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228227 q = 0) : d229909 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228227, d229909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228227, d229909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228228 q = 0) : d229910 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228228, d229910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228228, d229910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228229 q = 0) : d229911 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228229, d229911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228229, d229911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22620 (p : Pattern) (selected : d228235 p = 0) : d229917 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228152 q = 0) : d229864 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228152, d229864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22603 q selected
    | true =>
      simp only [d228152, d229864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22604 q selected
  have h2 (q : Pattern) (selected : d228153 q = 0) : d229865 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228153, d229865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228153, d229865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228154 q = 0) : d229866 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228154, d229866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228154, d229866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228155 q = 0) : d229867 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228155, d229867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228155, d229867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228162 q = 0) : d229874 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228162, d229874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22605 q selected
    | true =>
      simp only [d228162, d229874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22606 q selected
  have h6 (q : Pattern) (selected : d228163 q = 0) : d229875 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228163, d229875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228163, d229875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228164 q = 0) : d229876 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228164, d229876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228164, d229876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228185 q = 0) : d229897 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228185, d229897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22610 q selected
    | true =>
      simp only [d228185, d229897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22597 q selected
  have h9 (q : Pattern) (selected : d228215 q = 0) : d229841 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228215, d229841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22615 q selected
    | true =>
      simp only [d228215, d229841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22616 q selected
  have h10 (q : Pattern) (selected : d228216 q = 0) : d229898 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228216, d229898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d228216, d229898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d228230 q = 0) : d229912 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228230, d229912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22619 q selected
    | true =>
      simp only [d228230, d229912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d228231 q = 0) : d229913 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228231, d229913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d228231, d229913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d228232 q = 0) : d229914 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228232, d229914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d228232, d229914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d228233 q = 0) : d229915 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228233, d229915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228233, d229915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d228234 q = 0) : d229916 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228234, d229916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228234, d229916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d228235 q = 0) : d229917 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228235, d229917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228235, d229917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro22621 (p : Pattern) (selected : d228236 p = 0) : d229918 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228115 q = 0) : d229827 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228115, d229827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22595 q selected
    | true =>
      simp only [d228115, d229827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228116 q = 0) : d229828 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228116, d229828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228116, d229828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228119 q = 0) : d229831 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228119, d229831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22596 q selected
    | true =>
      simp only [d228119, d229831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228120 q = 0) : d229832 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228120, d229832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228120, d229832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228121 q = 0) : d229833 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228121, d229833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228121, d229833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228122 q = 0) : d229834 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228122, d229834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228122, d229834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228148 q = 0) : d229860 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228148, d229860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228148, d229860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228236 q = 0) : d229918 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228236, d229918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228236, d229918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22622 (p : Pattern) (selected : d228237 p = 0) : d229919 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228119 q = 0) : d229831 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228119, d229831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22596 q selected
    | true =>
      simp only [d228119, d229831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228120 q = 0) : d229832 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228120, d229832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228120, d229832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228125 q = 0) : d229837 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228125, d229837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228125, d229837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228126 q = 0) : d229838 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228126, d229838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228126, d229838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228150 q = 0) : d229862 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228150, d229862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228150, d229862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228237 q = 0) : d229919 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228237, d229919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228237, d229919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22623 (p : Pattern) (selected : d228242 p = 0) : d229924 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228115 q = 0) : d229827 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228115, d229827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22595 q selected
    | true =>
      simp only [d228115, d229827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228116 q = 0) : d229828 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228116, d229828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228116, d229828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228119 q = 0) : d229831 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228119, d229831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22596 q selected
    | true =>
      simp only [d228119, d229831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228120 q = 0) : d229832 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228120, d229832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228120, d229832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228121 q = 0) : d229833 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228121, d229833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228121, d229833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228156 q = 0) : d229868 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228156, d229868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228156, d229868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228157 q = 0) : d229869 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228157, d229869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228157, d229869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228242 q = 0) : d229924 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228242, d229924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228242, d229924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22624 (p : Pattern) (selected : d228243 p = 0) : d229925 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228119 q = 0) : d229831 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228119, d229831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22596 q selected
    | true =>
      simp only [d228119, d229831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228120 q = 0) : d229832 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228120, d229832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228120, d229832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228125 q = 0) : d229837 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228125, d229837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228125, d229837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228159 q = 0) : d229871 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228159, d229871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228159, d229871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228160 q = 0) : d229872 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228160, d229872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228160, d229872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228243 q = 0) : d229925 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228243, d229925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228243, d229925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22625 (p : Pattern) (selected : d228247 p = 0) : d229929 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228179 q = 0) : d229891 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228179, d229891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22609 q selected
    | true =>
      simp only [d228179, d229891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228180 q = 0) : d229892 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228180, d229892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228180, d229892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228115 q = 0) : d229827 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228115, d229827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22595 q selected
    | true =>
      simp only [d228115, d229827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228116 q = 0) : d229828 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228116, d229828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228116, d229828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228181 q = 0) : d229893 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228181, d229893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228181, d229893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228182 q = 0) : d229894 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228182, d229894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228182, d229894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228183 q = 0) : d229895 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228183, d229895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228183, d229895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228247 q = 0) : d229929 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228247, d229929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228247, d229929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22626 (p : Pattern) (selected : d228249 p = 0) : d229849 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228201 q = 0) : d229827 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228201, d229827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22613 q selected
    | true =>
      simp only [d228201, d229827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228202 q = 0) : d229828 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228202, d229828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228202, d229828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228205 q = 0) : d229831 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228205, d229831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22614 q selected
    | true =>
      simp only [d228205, d229831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228206 q = 0) : d229832 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228206, d229832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228206, d229832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228207 q = 0) : d229833 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228207, d229833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228207, d229833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228208 q = 0) : d229834 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228208, d229834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228208, d229834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228209 q = 0) : d229835 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228209, d229835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228209, d229835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228249 q = 0) : d229849 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228249, d229849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228249, d229849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22627 (p : Pattern) (selected : d228250 p = 0) : d229850 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228205 q = 0) : d229831 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228205, d229831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22614 q selected
    | true =>
      simp only [d228205, d229831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228206 q = 0) : d229832 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228206, d229832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228206, d229832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228211 q = 0) : d229837 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228211, d229837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228211, d229837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228212 q = 0) : d229838 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228212, d229838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228212, d229838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228213 q = 0) : d229839 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228213, d229839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228213, d229839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228250 q = 0) : d229850 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228250, d229850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228250, d229850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22628 (p : Pattern) (selected : d228253 p = 0) : d229932 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228224 q = 0) : d229906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228224, d229906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22618 q selected
    | true =>
      simp only [d228224, d229906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228225 q = 0) : d229907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228225, d229907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228225, d229907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228226 q = 0) : d229908 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228226, d229908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228226, d229908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228227 q = 0) : d229909 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228227, d229909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228227, d229909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228228 q = 0) : d229910 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228228, d229910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228228, d229910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228253 q = 0) : d229932 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228253, d229932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228253, d229932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22629 (p : Pattern) (selected : d228259 p = 0) : d229938 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228152 q = 0) : d229864 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228152, d229864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22603 q selected
    | true =>
      simp only [d228152, d229864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22604 q selected
  have h2 (q : Pattern) (selected : d228153 q = 0) : d229865 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228153, d229865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228153, d229865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228154 q = 0) : d229866 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228154, d229866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228154, d229866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228155 q = 0) : d229867 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228155, d229867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228155, d229867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228162 q = 0) : d229874 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228162, d229874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22605 q selected
    | true =>
      simp only [d228162, d229874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22606 q selected
  have h6 (q : Pattern) (selected : d228163 q = 0) : d229875 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228163, d229875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228163, d229875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228164 q = 0) : d229876 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228164, d229876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228164, d229876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228185 q = 0) : d229897 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228185, d229897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22610 q selected
    | true =>
      simp only [d228185, d229897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22597 q selected
  have h9 (q : Pattern) (selected : d228215 q = 0) : d229841 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228215, d229841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22615 q selected
    | true =>
      simp only [d228215, d229841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22616 q selected
  have h10 (q : Pattern) (selected : d228216 q = 0) : d229898 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228216, d229898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d228216, d229898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d228230 q = 0) : d229912 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228230, d229912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22619 q selected
    | true =>
      simp only [d228230, d229912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d228231 q = 0) : d229913 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228231, d229913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d228231, d229913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d228232 q = 0) : d229914 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228232, d229914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d228232, d229914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d228233 q = 0) : d229915 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228233, d229915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228233, d229915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d228234 q = 0) : d229916 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228234, d229916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228234, d229916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d228238 q = 0) : d229920 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228238, d229920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22621 q selected
    | true =>
      simp only [d228238, d229920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22622 q selected
  have h17 (q : Pattern) (selected : d228239 q = 0) : d229921 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228239, d229921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228239, d229921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d228240 q = 0) : d229922 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228240, d229922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d228240, d229922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d228241 q = 0) : d229923 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228241, d229923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228241, d229923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d228244 q = 0) : d229926 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228244, d229926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22623 q selected
    | true =>
      simp only [d228244, d229926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22624 q selected
  have h21 (q : Pattern) (selected : d228245 q = 0) : d229927 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228245, d229927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228245, d229927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d228246 q = 0) : d229928 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228246, d229928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d228246, d229928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d228248 q = 0) : d229930 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228248, d229930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22625 q selected
    | true =>
      simp only [d228248, d229930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22600 q selected
  have h24 (q : Pattern) (selected : d228251 q = 0) : d229851 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228251, d229851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22626 q selected
    | true =>
      simp only [d228251, d229851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22627 q selected
  have h25 (q : Pattern) (selected : d228252 q = 0) : d229931 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228252, d229931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d228252, d229931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d228254 q = 0) : d229933 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228254, d229933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22628 q selected
    | true =>
      simp only [d228254, d229933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d228255 q = 0) : d229934 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228255, d229934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d228255, d229934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d228256 q = 0) : d229935 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228256, d229935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d228256, d229935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d228257 q = 0) : d229936 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228257, d229936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d228257, d229936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d228258 q = 0) : d229937 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228258, d229937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d228258, d229937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d228259 q = 0) : d229938 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228259, d229938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d228259, d229938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro22630 (p : Pattern) (selected : d228266 p = 0) : d229945 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228129 q = 0) : d229841 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228129, d229841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22597 q selected
    | true =>
      simp only [d228129, d229841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22598 q selected
  have h2 (q : Pattern) (selected : d228130 q = 0) : d229842 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228130, d229842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228130, d229842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228131 q = 0) : d229843 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228131, d229843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228131, d229843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228132 q = 0) : d229844 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228132, d229844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228132, d229844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228133 q = 0) : d229845 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228133, d229845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228133, d229845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228261 q = 0) : d229940 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228261, d229940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22598 q selected
    | true =>
      simp only [d228261, d229940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228262 q = 0) : d229941 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228262, d229941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228262, d229941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228263 q = 0) : d229942 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228263, d229942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228263, d229942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228264 q = 0) : d229943 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228264, d229943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228264, d229943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228265 q = 0) : d229944 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228265, d229944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228265, d229944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d228266 q = 0) : d229945 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228266, d229945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228266, d229945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22631 (p : Pattern) (selected : d228272 p = 0) : d229951 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228261 q = 0) : d229940 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228261, d229940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22598 q selected
    | true =>
      simp only [d228261, d229940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228262 q = 0) : d229941 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228262, d229941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228262, d229941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228263 q = 0) : d229942 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228263, d229942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228263, d229942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228264 q = 0) : d229943 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228264, d229943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228264, d229943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228265 q = 0) : d229944 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228265, d229944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228265, d229944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228267 q = 0) : d229946 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228267, d229946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22601 q selected
    | true =>
      simp only [d228267, d229946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228268 q = 0) : d229947 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228268, d229947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228268, d229947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228269 q = 0) : d229948 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228269, d229948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228269, d229948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228270 q = 0) : d229949 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228270, d229949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228270, d229949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228271 q = 0) : d229950 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228271, d229950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228271, d229950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d228272 q = 0) : d229951 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228272, d229951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228272, d229951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22632 (p : Pattern) (selected : d228279 p = 0) : d229958 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228248 q = 0) : d229930 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228248, d229930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22625 q selected
    | true =>
      simp only [d228248, d229930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22600 q selected
  have h2 (q : Pattern) (selected : d228251 q = 0) : d229851 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228251, d229851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22626 q selected
    | true =>
      simp only [d228251, d229851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22627 q selected
  have h3 (q : Pattern) (selected : d228252 q = 0) : d229931 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228252, d229931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228252, d229931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228254 q = 0) : d229933 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228254, d229933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22628 q selected
    | true =>
      simp only [d228254, d229933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228255 q = 0) : d229934 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228255, d229934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228255, d229934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228256 q = 0) : d229935 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228256, d229935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228256, d229935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228277 q = 0) : d229956 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228277, d229956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228277, d229956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228278 q = 0) : d229957 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228278, d229957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228278, d229957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d228279 q = 0) : d229958 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228279, d229958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228279, d229958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro22633 (p : Pattern) (selected : d228281 p = 0) : d229960 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228267 q = 0) : d229946 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228267, d229946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22601 q selected
    | true =>
      simp only [d228267, d229946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228268 q = 0) : d229947 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228268, d229947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228268, d229947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228269 q = 0) : d229948 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228269, d229948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228269, d229948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228270 q = 0) : d229949 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228270, d229949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228270, d229949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228271 q = 0) : d229950 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228271, d229950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228271, d229950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228281 q = 0) : d229960 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228281, d229960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228281, d229960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22634 (p : Pattern) (selected : d228292 p = 0) : d229971 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228287 q = 0) : d229966 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228287, d229966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228287, d229966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22607 q selected
  have h2 (q : Pattern) (selected : d228167 q = 0) : d229879 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228167, d229879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22607 q selected
    | true =>
      simp only [d228167, d229879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228288 q = 0) : d229967 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228288, d229967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228288, d229967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228168 q = 0) : d229880 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228168, d229880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228168, d229880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228289 q = 0) : d229968 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228289, d229968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228289, d229968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228290 q = 0) : d229969 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228290, d229969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228290, d229969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228044 q = 0) : d229775 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228044, d229775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228044, d229775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22565 q selected
  have h8 (q : Pattern) (selected : d227956 q = 0) : d229710 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227956, d229710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22565 q selected
    | true =>
      simp only [d227956, d229710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228045 q = 0) : d229776 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228045, d229776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228045, d229776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227957 q = 0) : d229711 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227957, d229711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d227957, d229711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d228046 q = 0) : d229777 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228046, d229777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228046, d229777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d228047 q = 0) : d229778 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228047, d229778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d228047, d229778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d228291 q = 0) : d229970 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228291, d229970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228291, d229970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d227872 q = 0) : d229645 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227872, d229645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227872, d229645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22536 q selected
  have h15 (q : Pattern) (selected : d227795 q = 0) : d229591 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227795, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22536 q selected
    | true =>
      simp only [d227795, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d227873 q = 0) : d229646 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227873, d229646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d227873, d229646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d227796 q = 0) : d229592 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227796, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d227796, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d227874 q = 0) : d229647 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227874, d229647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d227874, d229647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d227875 q = 0) : d229648 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227875, d229648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d227875, d229648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d228048 q = 0) : d229779 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228048, d229779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d228048, d229779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d228292 q = 0) : d229971 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228292, d229971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d228292, d229971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro22635 (p : Pattern) (selected : d228298 p = 0) : d229977 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228293 q = 0) : d229972 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228293, d229972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22634 q selected
    | true =>
      simp only [d228293, d229972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22584 q selected
  have h2 (q : Pattern) (selected : d228294 q = 0) : d229973 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228294, d229973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228294, d229973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228295 q = 0) : d229974 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228295, d229974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228295, d229974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228050 q = 0) : d229781 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228050, d229781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22584 q selected
    | true =>
      simp only [d228050, d229781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22552 q selected
  have h5 (q : Pattern) (selected : d228051 q = 0) : d229782 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228051, d229782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228051, d229782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228052 q = 0) : d229783 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228052, d229783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228052, d229783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228296 q = 0) : d229975 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228296, d229975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228296, d229975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d227878 q = 0) : d229651 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d227878, d229651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22552 q selected
    | true =>
      simp only [d227878, d229651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22527 q selected
  have h9 (q : Pattern) (selected : d227879 q = 0) : d229652 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d227879, d229652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227879, d229652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227880 q = 0) : d229653 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d227880, d229653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227880, d229653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d228053 q = 0) : d229784 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228053, d229784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228053, d229784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d228297 q = 0) : d229976 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228297, d229976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228297, d229976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d228298 q = 0) : d229977 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228298, d229977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d228298, d229977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro22636 (p : Pattern) (selected : d228303 p = 0) : d229982 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228050 q = 0) : d229781 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228050, d229781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22584 q selected
    | true =>
      simp only [d228050, d229781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22552 q selected
  have h2 (q : Pattern) (selected : d228051 q = 0) : d229782 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228051, d229782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228051, d229782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228052 q = 0) : d229783 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228052, d229783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228052, d229783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227878 q = 0) : d229651 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d227878, d229651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22552 q selected
    | true =>
      simp only [d227878, d229651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22527 q selected
  have h5 (q : Pattern) (selected : d227879 q = 0) : d229652 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d227879, d229652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227879, d229652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227880 q = 0) : d229653 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d227880, d229653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227880, d229653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228053 q = 0) : d229784 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228053, d229784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228053, d229784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228301 q = 0) : d229980 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228301, d229980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228301, d229980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228302 q = 0) : d229981 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228302, d229981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228302, d229981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228303 q = 0) : d229982 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228303, d229982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228303, d229982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22637 (p : Pattern) (selected : d228309 p = 0) : d229988 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228299 q = 0) : d229978 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228299, d229978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22635 q selected
    | true =>
      simp only [d228299, d229978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228300 q = 0) : d229979 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228300, d229979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228300, d229979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228304 q = 0) : d229983 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228304, d229983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22636 q selected
    | true =>
      simp only [d228304, d229983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228305 q = 0) : d229984 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228305, d229984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228305, d229984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228306 q = 0) : d229985 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228306, d229985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228306, d229985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228307 q = 0) : d229986 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228307, d229986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228307, d229986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228308 q = 0) : d229987 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228308, d229987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228308, d229987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228309 q = 0) : d229988 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228309, d229988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228309, d229988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22638 (p : Pattern) (selected : d228311 p = 0) : d229990 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227878 q = 0) : d229651 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d227878, d229651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22552 q selected
    | true =>
      simp only [d227878, d229651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22527 q selected
  have h2 (q : Pattern) (selected : d227879 q = 0) : d229652 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d227879, d229652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227879, d229652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d227880 q = 0) : d229653 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d227880, d229653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227880, d229653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228301 q = 0) : d229980 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228301, d229980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228301, d229980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228310 q = 0) : d229989 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228310, d229989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228310, d229989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228311 q = 0) : d229990 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228311, d229990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228311, d229990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22639 (p : Pattern) (selected : d228317 p = 0) : d229996 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228304 q = 0) : d229983 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228304, d229983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22636 q selected
    | true =>
      simp only [d228304, d229983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228305 q = 0) : d229984 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228305, d229984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228305, d229984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228312 q = 0) : d229991 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228312, d229991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22638 q selected
    | true =>
      simp only [d228312, d229991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228313 q = 0) : d229992 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228313, d229992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228313, d229992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228314 q = 0) : d229993 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228314, d229993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228314, d229993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228315 q = 0) : d229994 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228315, d229994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228315, d229994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228316 q = 0) : d229995 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228316, d229995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228316, d229995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228317 q = 0) : d229996 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228317, d229996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228317, d229996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22640 (p : Pattern) (selected : d228324 p = 0) : d229780 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228319 q = 0) : d229775 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228319, d229775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228319, d229775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22611 q selected
  have h2 (q : Pattern) (selected : d228188 q = 0) : d229710 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228188, d229710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22611 q selected
    | true =>
      simp only [d228188, d229710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228320 q = 0) : d229776 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228320, d229776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228320, d229776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228189 q = 0) : d229711 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228189, d229711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228189, d229711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228321 q = 0) : d229777 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228321, d229777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228321, d229777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228322 q = 0) : d229778 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228322, d229778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228322, d229778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228063 q = 0) : d229645 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228063, d229645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228063, d229645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22569 q selected
  have h8 (q : Pattern) (selected : d227977 q = 0) : d229591 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227977, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22569 q selected
    | true =>
      simp only [d227977, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228064 q = 0) : d229646 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228064, d229646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228064, d229646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227978 q = 0) : d229592 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227978, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d227978, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d228065 q = 0) : d229647 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228065, d229647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228065, d229647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d228066 q = 0) : d229648 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228066, d229648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d228066, d229648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d228323 q = 0) : d229779 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228323, d229779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228323, d229779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d227891 q = 0) : d229527 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227891, d229527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227891, d229527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22540 q selected
  have h15 (q : Pattern) (selected : d227816 q = 0) : d229486 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227816, d229486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22540 q selected
    | true =>
      simp only [d227816, d229486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d227892 q = 0) : d229528 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227892, d229528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d227892, d229528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d227817 q = 0) : d229487 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227817, d229487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d227817, d229487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d227893 q = 0) : d229529 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227893, d229529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d227893, d229529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d227894 q = 0) : d229530 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227894, d229530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d227894, d229530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d228067 q = 0) : d229649 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228067, d229649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d228067, d229649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d228324 q = 0) : d229780 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228324, d229780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d228324, d229780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro22641 (p : Pattern) (selected : d228331 p = 0) : d229982 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228325 q = 0) : d229781 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228325, d229781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22640 q selected
    | true =>
      simp only [d228325, d229781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22587 q selected
  have h2 (q : Pattern) (selected : d228326 q = 0) : d229782 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228326, d229782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228326, d229782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228327 q = 0) : d229783 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228327, d229783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228327, d229783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228069 q = 0) : d229651 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228069, d229651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22587 q selected
    | true =>
      simp only [d228069, d229651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22555 q selected
  have h5 (q : Pattern) (selected : d228070 q = 0) : d229652 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228070, d229652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228070, d229652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228071 q = 0) : d229653 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228071, d229653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228071, d229653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228328 q = 0) : d229784 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228328, d229784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228328, d229784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228329 q = 0) : d229980 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228329, d229980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228329, d229980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228330 q = 0) : d229981 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228330, d229981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228330, d229981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228331 q = 0) : d229982 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228331, d229982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228331, d229982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22642 (p : Pattern) (selected : d228335 p = 0) : d229990 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228069 q = 0) : d229651 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228069, d229651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22587 q selected
    | true =>
      simp only [d228069, d229651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22555 q selected
  have h2 (q : Pattern) (selected : d228070 q = 0) : d229652 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228070, d229652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228070, d229652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228071 q = 0) : d229653 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228071, d229653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228071, d229653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228329 q = 0) : d229980 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228329, d229980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228329, d229980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228334 q = 0) : d229989 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228334, d229989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228334, d229989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228335 q = 0) : d229990 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228335, d229990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228335, d229990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22643 (p : Pattern) (selected : d228341 p = 0) : d229996 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228332 q = 0) : d229983 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228332, d229983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22641 q selected
    | true =>
      simp only [d228332, d229983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228333 q = 0) : d229984 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228333, d229984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228333, d229984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228336 q = 0) : d229991 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228336, d229991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22642 q selected
    | true =>
      simp only [d228336, d229991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228337 q = 0) : d229992 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228337, d229992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228337, d229992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228338 q = 0) : d229993 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228338, d229993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228338, d229993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228339 q = 0) : d229994 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228339, d229994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228339, d229994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228340 q = 0) : d229995 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228340, d229995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228340, d229995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228341 q = 0) : d229996 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228341, d229996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228341, d229996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22644 (p : Pattern) (selected : d228345 p = 0) : d230001 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228336 q = 0) : d229991 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228336, d229991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22642 q selected
    | true =>
      simp only [d228336, d229991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228337 q = 0) : d229992 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228337, d229992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228337, d229992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228342 q = 0) : d229998 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228342, d229998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228342, d229998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228343 q = 0) : d229999 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228343, d229999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228343, d229999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228344 q = 0) : d230000 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228344, d230000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228344, d230000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228345 q = 0) : d230001 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228345, d230001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228345, d230001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22645 (p : Pattern) (selected : d228348 p = 0) : d230004 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227872 q = 0) : d229645 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227872, d229645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227872, d229645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22536 q selected
  have h2 (q : Pattern) (selected : d227795 q = 0) : d229591 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227795, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22536 q selected
    | true =>
      simp only [d227795, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d227873 q = 0) : d229646 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227873, d229646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227873, d229646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227796 q = 0) : d229592 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227796, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227796, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227874 q = 0) : d229647 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227874, d229647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227874, d229647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227875 q = 0) : d229648 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227875, d229648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227875, d229648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d227731 q = 0) : d229527 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227731, d229527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227731, d229527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22519 q selected
  have h8 (q : Pattern) (selected : d227690 q = 0) : d229486 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227690, d229486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22519 q selected
    | true =>
      simp only [d227690, d229486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d227732 q = 0) : d229528 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227732, d229528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227732, d229528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227691 q = 0) : d229487 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227691, d229487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d227691, d229487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d227733 q = 0) : d229529 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227733, d229529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d227733, d229529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d227734 q = 0) : d229530 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227734, d229530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d227734, d229530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d227876 q = 0) : d229649 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d227876, d229649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d227876, d229649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d228348 q = 0) : d230004 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228348, d230004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d228348, d230004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h14 p selected
theorem eqIntro22646 (p : Pattern) (selected : d228354 p = 0) : d230010 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228050 q = 0) : d229781 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228050, d229781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22584 q selected
    | true =>
      simp only [d228050, d229781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22552 q selected
  have h2 (q : Pattern) (selected : d228051 q = 0) : d229782 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228051, d229782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228051, d229782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228052 q = 0) : d229783 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228052, d229783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228052, d229783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227878 q = 0) : d229651 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d227878, d229651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22552 q selected
    | true =>
      simp only [d227878, d229651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22527 q selected
  have h5 (q : Pattern) (selected : d227879 q = 0) : d229652 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d227879, d229652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227879, d229652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227880 q = 0) : d229653 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d227880, d229653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227880, d229653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228053 q = 0) : d229784 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228053, d229784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228053, d229784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228349 q = 0) : d230005 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228349, d230005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22645 q selected
    | true =>
      simp only [d228349, d230005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228350 q = 0) : d230006 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228350, d230006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228350, d230006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228351 q = 0) : d230007 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228351, d230007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228351, d230007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d228352 q = 0) : d230008 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228352, d230008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d228352, d230008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d228353 q = 0) : d230009 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228353, d230009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228353, d230009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d228354 q = 0) : d230010 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228354, d230010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d228354, d230010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro22647 (p : Pattern) (selected : d228360 p = 0) : d230016 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228355 q = 0) : d230011 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228355, d230011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22646 q selected
    | true =>
      simp only [d228355, d230011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228356 q = 0) : d230012 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228356, d230012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228356, d230012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228357 q = 0) : d230013 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228357, d230013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228357, d230013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228358 q = 0) : d230014 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228358, d230014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228358, d230014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228359 q = 0) : d230015 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228359, d230015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228359, d230015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228360 q = 0) : d230016 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228360, d230016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228360, d230016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22648 (p : Pattern) (selected : d228366 p = 0) : d230022 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228318 q = 0) : d229997 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228318, d229997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22637 q selected
    | true =>
      simp only [d228318, d229997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22639 q selected
  have h2 (q : Pattern) (selected : d228346 q = 0) : d230002 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228346, d230002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22643 q selected
    | true =>
      simp only [d228346, d230002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22644 q selected
  have h3 (q : Pattern) (selected : d228347 q = 0) : d230003 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228347, d230003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228347, d230003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228361 q = 0) : d230017 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228361, d230017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22647 q selected
    | true =>
      simp only [d228361, d230017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228362 q = 0) : d230018 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228362, d230018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228362, d230018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228363 q = 0) : d230019 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228363, d230019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228363, d230019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228364 q = 0) : d230020 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228364, d230020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228364, d230020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228365 q = 0) : d230021 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228365, d230021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228365, d230021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d228366 q = 0) : d230022 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228366, d230022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228366, d230022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro22649 (p : Pattern) (selected : d228371 p = 0) : d230001 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228312 q = 0) : d229991 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228312, d229991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22638 q selected
    | true =>
      simp only [d228312, d229991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228313 q = 0) : d229992 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228313, d229992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228313, d229992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228368 q = 0) : d229998 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228368, d229998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228368, d229998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228369 q = 0) : d229999 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228369, d229999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228369, d229999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228370 q = 0) : d230000 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228370, d230000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228370, d230000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228371 q = 0) : d230001 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228371, d230001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228371, d230001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22650 (p : Pattern) (selected : d228377 p = 0) : d230029 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228372 q = 0) : d230024 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228372, d230024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22649 q selected
    | true =>
      simp only [d228372, d230024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228373 q = 0) : d230025 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228373, d230025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228373, d230025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228374 q = 0) : d230026 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228374, d230026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228374, d230026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228375 q = 0) : d230027 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228375, d230027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228375, d230027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228376 q = 0) : d230028 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228376, d230028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228376, d230028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228377 q = 0) : d230029 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228377, d230029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228377, d230029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22651 (p : Pattern) (selected : d228383 p = 0) : d230035 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228135 q = 0) : d229847 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228135, d229847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228135, d229847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22599 q selected
  have h2 (q : Pattern) (selected : d228136 q = 0) : d229848 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d228136, d229848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228136, d229848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228145 q = 0) : d229857 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228145, d229857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22599 q selected
    | true =>
      simp only [d228145, d229857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22602 q selected
  have h4 (q : Pattern) (selected : d228146 q = 0) : d229858 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d228146, d229858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228146, d229858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228147 q = 0) : d229859 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d228147, d229859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228147, d229859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228260 q = 0) : d229939 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228260, d229939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22620 q selected
    | true =>
      simp only [d228260, d229939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22629 q selected
  have h7 (q : Pattern) (selected : d228273 q = 0) : d229952 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228273, d229952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22630 q selected
    | true =>
      simp only [d228273, d229952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22631 q selected
  have h8 (q : Pattern) (selected : d228274 q = 0) : d229953 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d228274, d229953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228274, d229953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d228275 q = 0) : d229954 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d228275, d229954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d228275, d229954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d228276 q = 0) : d229955 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d228276, d229955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228276, d229955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d228280 q = 0) : d229959 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228280, d229959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228280, d229959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22632 q selected
  have h12 (q : Pattern) (selected : d228282 q = 0) : d229961 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228282, d229961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228282, d229961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22633 q selected
  have h13 (q : Pattern) (selected : d228283 q = 0) : d229962 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d228283, d229962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d228283, d229962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d228284 q = 0) : d229963 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d228284, d229963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d228284, d229963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d228285 q = 0) : d229964 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d228285, d229964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d228285, d229964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d228286 q = 0) : d229965 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d228286, d229965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d228286, d229965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d228367 q = 0) : d230023 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228367, d230023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228367, d230023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22648 q selected
  have h18 (q : Pattern) (selected : d228378 q = 0) : d230030 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228378, d230030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228378, d230030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22650 q selected
  have h19 (q : Pattern) (selected : d228379 q = 0) : d230031 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d228379, d230031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d228379, d230031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d228380 q = 0) : d230032 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d228380, d230032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d228380, d230032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d228381 q = 0) : d230033 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d228381, d230033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d228381, d230033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d228382 q = 0) : d230034 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d228382, d230034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d228382, d230034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d228383 q = 0) : d230035 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d228383, d230035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d228383, d230035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro22652 (p : Pattern) (selected : d228389 p = 0) : d230041 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228384 q = 0) : d230036 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d228384, d230036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228384, d230036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22651 q selected
  have h2 (q : Pattern) (selected : d228385 q = 0) : d230037 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d228385, d230037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228385, d230037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228386 q = 0) : d230038 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d228386, d230038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228386, d230038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228387 q = 0) : d230039 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d228387, d230039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228387, d230039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228388 q = 0) : d230040 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d228388, d230040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228388, d230040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228389 q = 0) : d230041 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d228389, d230041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228389, d230041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22653 (p : Pattern) (selected : d228393 p = 0) : d230045 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227956 q = 0) : d229710 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227956, d229710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22565 q selected
    | true =>
      simp only [d227956, d229710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227957 q = 0) : d229711 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227957, d229711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227957, d229711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d227958 q = 0) : d229712 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227958, d229712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227958, d229712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227959 q = 0) : d229713 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227959, d229713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227959, d229713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227795 q = 0) : d229591 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227795, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22536 q selected
    | true =>
      simp only [d227795, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d227796 q = 0) : d229592 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227796, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227796, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d227797 q = 0) : d229593 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227797, d229593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227797, d229593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d227798 q = 0) : d229594 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227798, d229594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227798, d229594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d227960 q = 0) : d229714 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d227960, d229714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227960, d229714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228392 q = 0) : d230044 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228392, d230044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d228392, d230044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d228393 q = 0) : d230045 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228393, d230045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228393, d230045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22654 (p : Pattern) (selected : d228397 p = 0) : d230049 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227795 q = 0) : d229591 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227795, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22536 q selected
    | true =>
      simp only [d227795, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227796 q = 0) : d229592 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227796, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227796, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d227797 q = 0) : d229593 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227797, d229593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227797, d229593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227798 q = 0) : d229594 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227798, d229594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227798, d229594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228392 q = 0) : d230044 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228392, d230044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228392, d230044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228397 q = 0) : d230049 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228397, d230049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228397, d230049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22655 (p : Pattern) (selected : d228404 p = 0) : d230056 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228394 q = 0) : d230046 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228394, d230046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22608 q selected
    | true =>
      simp only [d228394, d230046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22653 q selected
  have h2 (q : Pattern) (selected : d228395 q = 0) : d230047 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228395, d230047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228395, d230047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228396 q = 0) : d230048 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228396, d230048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228396, d230048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228398 q = 0) : d230050 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228398, d230050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22653 q selected
    | true =>
      simp only [d228398, d230050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22654 q selected
  have h5 (q : Pattern) (selected : d228399 q = 0) : d230051 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228399, d230051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228399, d230051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228400 q = 0) : d230052 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228400, d230052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228400, d230052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228401 q = 0) : d230053 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228401, d230053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228401, d230053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228402 q = 0) : d230054 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228402, d230054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228402, d230054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228403 q = 0) : d230055 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228403, d230055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228403, d230055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228404 q = 0) : d230056 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228404, d230056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228404, d230056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22656 (p : Pattern) (selected : d228408 p = 0) : d230060 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228398 q = 0) : d230050 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228398, d230050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22653 q selected
    | true =>
      simp only [d228398, d230050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22654 q selected
  have h2 (q : Pattern) (selected : d228399 q = 0) : d230051 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228399, d230051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228399, d230051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228400 q = 0) : d230052 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228400, d230052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228400, d230052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228402 q = 0) : d230054 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228402, d230054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228402, d230054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228407 q = 0) : d230059 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228407, d230059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228407, d230059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228408 q = 0) : d230060 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228408, d230060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228408, d230060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22657 (p : Pattern) (selected : d228414 p = 0) : d230066 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228405 q = 0) : d230057 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228405, d230057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22655 q selected
    | true =>
      simp only [d228405, d230057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228406 q = 0) : d230058 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228406, d230058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228406, d230058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228409 q = 0) : d230061 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228409, d230061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22656 q selected
    | true =>
      simp only [d228409, d230061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228410 q = 0) : d230062 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228410, d230062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228410, d230062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228411 q = 0) : d230063 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228411, d230063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228411, d230063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228412 q = 0) : d230064 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228412, d230064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228412, d230064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228413 q = 0) : d230065 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228413, d230065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228413, d230065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228414 q = 0) : d230066 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228414, d230066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228414, d230066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22658 (p : Pattern) (selected : d228418 p = 0) : d230070 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228409 q = 0) : d230061 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228409, d230061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22656 q selected
    | true =>
      simp only [d228409, d230061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228410 q = 0) : d230062 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228410, d230062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228410, d230062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228415 q = 0) : d230067 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228415, d230067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228415, d230067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228416 q = 0) : d230068 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228416, d230068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228416, d230068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228417 q = 0) : d230069 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228417, d230069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228417, d230069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228418 q = 0) : d230070 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228418, d230070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228418, d230070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22659 (p : Pattern) (selected : d228424 p = 0) : d230076 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228419 q = 0) : d230071 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228419, d230071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22657 q selected
    | true =>
      simp only [d228419, d230071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22658 q selected
  have h2 (q : Pattern) (selected : d228420 q = 0) : d230072 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228420, d230072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228420, d230072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228421 q = 0) : d230073 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228421, d230073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228421, d230073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228422 q = 0) : d230074 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228422, d230074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228422, d230074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228423 q = 0) : d230075 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228423, d230075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228423, d230075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228424 q = 0) : d230076 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228424, d230076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228424, d230076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22660 (p : Pattern) (selected : d228427 p = 0) : d230079 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228405 q = 0) : d230057 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228405, d230057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22655 q selected
    | true =>
      simp only [d228405, d230057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228406 q = 0) : d230058 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228406, d230058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228406, d230058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228409 q = 0) : d230061 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228409, d230061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22656 q selected
    | true =>
      simp only [d228409, d230061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228410 q = 0) : d230062 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228410, d230062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228410, d230062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228411 q = 0) : d230063 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228411, d230063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228411, d230063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228412 q = 0) : d230064 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228412, d230064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228412, d230064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228413 q = 0) : d230065 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228413, d230065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228413, d230065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228427 q = 0) : d230079 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228427, d230079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228427, d230079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22661 (p : Pattern) (selected : d228428 p = 0) : d230080 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228409 q = 0) : d230061 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228409, d230061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22656 q selected
    | true =>
      simp only [d228409, d230061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228410 q = 0) : d230062 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228410, d230062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228410, d230062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228415 q = 0) : d230067 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228415, d230067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228415, d230067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228416 q = 0) : d230068 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228416, d230068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228416, d230068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228417 q = 0) : d230069 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228417, d230069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228417, d230069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228428 q = 0) : d230080 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228428, d230080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228428, d230080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22662 (p : Pattern) (selected : d228434 p = 0) : d230086 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228419 q = 0) : d230071 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228419, d230071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22657 q selected
    | true =>
      simp only [d228419, d230071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22658 q selected
  have h2 (q : Pattern) (selected : d228420 q = 0) : d230072 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228420, d230072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228420, d230072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228421 q = 0) : d230073 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228421, d230073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228421, d230073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228422 q = 0) : d230074 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228422, d230074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228422, d230074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228423 q = 0) : d230075 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228423, d230075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228423, d230075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228429 q = 0) : d230081 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228429, d230081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22660 q selected
    | true =>
      simp only [d228429, d230081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22661 q selected
  have h7 (q : Pattern) (selected : d228430 q = 0) : d230082 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228430, d230082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228430, d230082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228431 q = 0) : d230083 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228431, d230083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228431, d230083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228432 q = 0) : d230084 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228432, d230084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228432, d230084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228433 q = 0) : d230085 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228433, d230085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228433, d230085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d228434 q = 0) : d230086 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228434, d230086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228434, d230086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22663 (p : Pattern) (selected : d228439 p = 0) : d230091 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228405 q = 0) : d230057 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228405, d230057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22655 q selected
    | true =>
      simp only [d228405, d230057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228406 q = 0) : d230058 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228406, d230058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228406, d230058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228409 q = 0) : d230061 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228409, d230061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22656 q selected
    | true =>
      simp only [d228409, d230061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228410 q = 0) : d230062 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228410, d230062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228410, d230062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228411 q = 0) : d230063 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228411, d230063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228411, d230063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228412 q = 0) : d230064 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228412, d230064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228412, d230064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228438 q = 0) : d230090 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228438, d230090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228438, d230090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228439 q = 0) : d230091 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228439, d230091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228439, d230091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22664 (p : Pattern) (selected : d228441 p = 0) : d230093 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228409 q = 0) : d230061 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228409, d230061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22656 q selected
    | true =>
      simp only [d228409, d230061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228410 q = 0) : d230062 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228410, d230062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228410, d230062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228415 q = 0) : d230067 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228415, d230067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228415, d230067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228416 q = 0) : d230068 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228416, d230068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228416, d230068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228440 q = 0) : d230092 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228440, d230092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228440, d230092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228441 q = 0) : d230093 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228441, d230093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228441, d230093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22665 (p : Pattern) (selected : d228448 p = 0) : d230100 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228405 q = 0) : d230057 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228405, d230057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22655 q selected
    | true =>
      simp only [d228405, d230057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228406 q = 0) : d230058 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228406, d230058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228406, d230058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228409 q = 0) : d230061 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228409, d230061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22656 q selected
    | true =>
      simp only [d228409, d230061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228410 q = 0) : d230062 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228410, d230062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228410, d230062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228411 q = 0) : d230063 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228411, d230063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228411, d230063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228446 q = 0) : d230098 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228446, d230098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228446, d230098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228447 q = 0) : d230099 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228447, d230099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228447, d230099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228448 q = 0) : d230100 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228448, d230100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228448, d230100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22666 (p : Pattern) (selected : d228451 p = 0) : d230103 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228409 q = 0) : d230061 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228409, d230061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22656 q selected
    | true =>
      simp only [d228409, d230061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228410 q = 0) : d230062 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228410, d230062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228410, d230062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228415 q = 0) : d230067 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228415, d230067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228415, d230067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228449 q = 0) : d230101 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228449, d230101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228449, d230101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228450 q = 0) : d230102 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228450, d230102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228450, d230102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228451 q = 0) : d230103 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228451, d230103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228451, d230103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22667 (p : Pattern) (selected : d228456 p = 0) : d230108 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1204 q = 0) : d52785 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1204, d52785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro406 q selected
    | true =>
      simp only [d1204, d52785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1205 q = 0) : d52786 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1205, d52786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1205, d52786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d828 q = 0) : d52505 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d828, d52505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro334 q selected
    | true =>
      simp only [d828, d52505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d829 q = 0) : d52506 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d829, d52506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d829, d52506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1206 q = 0) : d52787 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1206, d52787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1206, d52787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228455 q = 0) : d230107 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d228455, d230107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228455, d230107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d537 q = 0) : d52284 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d537, d52284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro276 q selected
    | true =>
      simp only [d537, d52284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d538 q = 0) : d52285 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d538, d52285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d538, d52285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d830 q = 0) : d52507 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d830, d52507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d830, d52507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228165 q = 0) : d229877 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d228165, d229877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228165, d229877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d228456 q = 0) : d230108 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d228456, d230108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228456, d230108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22668 (p : Pattern) (selected : d228462 p = 0) : d230114 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228457 q = 0) : d230109 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228457, d230109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22667 q selected
    | true =>
      simp only [d228457, d230109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228458 q = 0) : d230110 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228458, d230110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228458, d230110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228459 q = 0) : d230111 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228459, d230111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228459, d230111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228460 q = 0) : d230112 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228460, d230112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228460, d230112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228167 q = 0) : d229879 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228167, d229879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22607 q selected
    | true =>
      simp only [d228167, d229879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228168 q = 0) : d229880 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228168, d229880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228168, d229880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228169 q = 0) : d229881 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228169, d229881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228169, d229881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228170 q = 0) : d229882 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228170, d229882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228170, d229882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228461 q = 0) : d230113 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228461, d230113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228461, d230113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227956 q = 0) : d229710 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227956, d229710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22565 q selected
    | true =>
      simp only [d227956, d229710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d227957 q = 0) : d229711 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227957, d229711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d227957, d229711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d227958 q = 0) : d229712 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227958, d229712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227958, d229712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d227959 q = 0) : d229713 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227959, d229713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d227959, d229713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d228171 q = 0) : d229883 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228171, d229883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d228171, d229883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d228462 q = 0) : d230114 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228462, d230114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228462, d230114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22669 (p : Pattern) (selected : d228468 p = 0) : d230120 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228463 q = 0) : d230115 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228463, d230115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22668 q selected
    | true =>
      simp only [d228463, d230115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22608 q selected
  have h2 (q : Pattern) (selected : d228464 q = 0) : d230116 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228464, d230116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228464, d230116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228465 q = 0) : d230117 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228465, d230117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228465, d230117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228394 q = 0) : d230046 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228394, d230046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22608 q selected
    | true =>
      simp only [d228394, d230046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22653 q selected
  have h5 (q : Pattern) (selected : d228395 q = 0) : d230047 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228395, d230047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228395, d230047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228396 q = 0) : d230048 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228396, d230048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228396, d230048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228466 q = 0) : d230118 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228466, d230118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228466, d230118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228398 q = 0) : d230050 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228398, d230050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22653 q selected
    | true =>
      simp only [d228398, d230050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22654 q selected
  have h9 (q : Pattern) (selected : d228399 q = 0) : d230051 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228399, d230051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228399, d230051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228400 q = 0) : d230052 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228400, d230052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228400, d230052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d228401 q = 0) : d230053 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228401, d230053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228401, d230053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d228467 q = 0) : d230119 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228467, d230119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228467, d230119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d228468 q = 0) : d230120 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228468, d230120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d228468, d230120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro22670 (p : Pattern) (selected : d228474 p = 0) : d230126 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228469 q = 0) : d230121 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228469, d230121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22669 q selected
    | true =>
      simp only [d228469, d230121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228470 q = 0) : d230122 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228470, d230122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228470, d230122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228405 q = 0) : d230057 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228405, d230057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22655 q selected
    | true =>
      simp only [d228405, d230057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228406 q = 0) : d230058 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228406, d230058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228406, d230058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228471 q = 0) : d230123 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228471, d230123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228471, d230123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228472 q = 0) : d230124 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228472, d230124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228472, d230124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228473 q = 0) : d230125 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228473, d230125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228473, d230125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228474 q = 0) : d230126 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228474, d230126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228474, d230126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22671 (p : Pattern) (selected : d228477 p = 0) : d229878 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1243 q = 0) : d52505 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1243, d52505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro413 q selected
    | true =>
      simp only [d1243, d52505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1244 q = 0) : d52506 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1244, d52506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1244, d52506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d862 q = 0) : d52284 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d862, d52284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro340 q selected
    | true =>
      simp only [d862, d52284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d863 q = 0) : d52285 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d863, d52285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d863, d52285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1245 q = 0) : d52507 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1245, d52507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1245, d52507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228476 q = 0) : d229877 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d228476, d229877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228476, d229877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d344 q = 0) : d51984 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d344, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro239 q selected
    | true =>
      simp only [d344, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d345 q = 0) : d51985 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d345, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d345, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d864 q = 0) : d52286 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d864, d52286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d864, d52286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228186 q = 0) : d229708 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d228186, d229708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228186, d229708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d228477 q = 0) : d229878 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d228477, d229878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228477, d229878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22672 (p : Pattern) (selected : d228483 p = 0) : d229884 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228478 q = 0) : d229879 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228478, d229879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22671 q selected
    | true =>
      simp only [d228478, d229879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228479 q = 0) : d229880 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228479, d229880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228479, d229880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228480 q = 0) : d229881 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228480, d229881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228480, d229881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228481 q = 0) : d229882 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228481, d229882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228481, d229882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228188 q = 0) : d229710 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228188, d229710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22611 q selected
    | true =>
      simp only [d228188, d229710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228189 q = 0) : d229711 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228189, d229711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228189, d229711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228190 q = 0) : d229712 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228190, d229712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228190, d229712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228191 q = 0) : d229713 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228191, d229713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228191, d229713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228482 q = 0) : d229883 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228482, d229883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228482, d229883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227977 q = 0) : d229591 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227977, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22569 q selected
    | true =>
      simp only [d227977, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d227978 q = 0) : d229592 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227978, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d227978, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d227979 q = 0) : d229593 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227979, d229593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227979, d229593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d227980 q = 0) : d229594 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227980, d229594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d227980, d229594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d228192 q = 0) : d229714 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228192, d229714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d228192, d229714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d228483 q = 0) : d229884 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228483, d229884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228483, d229884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22673 (p : Pattern) (selected : d228485 p = 0) : d230045 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228188 q = 0) : d229710 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228188, d229710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22611 q selected
    | true =>
      simp only [d228188, d229710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228189 q = 0) : d229711 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228189, d229711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228189, d229711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228190 q = 0) : d229712 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228190, d229712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228190, d229712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228191 q = 0) : d229713 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228191, d229713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228191, d229713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227977 q = 0) : d229591 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227977, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22569 q selected
    | true =>
      simp only [d227977, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d227978 q = 0) : d229592 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227978, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227978, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d227979 q = 0) : d229593 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227979, d229593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227979, d229593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d227980 q = 0) : d229594 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227980, d229594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227980, d229594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228192 q = 0) : d229714 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228192, d229714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228192, d229714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228484 q = 0) : d230044 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228484, d230044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d228484, d230044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d228485 q = 0) : d230045 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228485, d230045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228485, d230045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22674 (p : Pattern) (selected : d228489 p = 0) : d230049 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227977 q = 0) : d229591 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227977, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22569 q selected
    | true =>
      simp only [d227977, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227978 q = 0) : d229592 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227978, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227978, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d227979 q = 0) : d229593 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227979, d229593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227979, d229593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227980 q = 0) : d229594 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227980, d229594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227980, d229594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228484 q = 0) : d230044 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228484, d230044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228484, d230044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228489 q = 0) : d230049 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228489, d230049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228489, d230049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22675 (p : Pattern) (selected : d228496 p = 0) : d230056 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228486 q = 0) : d230046 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228486, d230046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22672 q selected
    | true =>
      simp only [d228486, d230046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22673 q selected
  have h2 (q : Pattern) (selected : d228487 q = 0) : d230047 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228487, d230047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228487, d230047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228488 q = 0) : d230048 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228488, d230048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228488, d230048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228490 q = 0) : d230050 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228490, d230050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22673 q selected
    | true =>
      simp only [d228490, d230050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22674 q selected
  have h5 (q : Pattern) (selected : d228491 q = 0) : d230051 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228491, d230051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228491, d230051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228492 q = 0) : d230052 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228492, d230052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228492, d230052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228493 q = 0) : d230053 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228493, d230053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228493, d230053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228494 q = 0) : d230054 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228494, d230054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228494, d230054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228495 q = 0) : d230055 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228495, d230055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228495, d230055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228496 q = 0) : d230056 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228496, d230056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228496, d230056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22676 (p : Pattern) (selected : d228500 p = 0) : d230060 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228490 q = 0) : d230050 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228490, d230050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22673 q selected
    | true =>
      simp only [d228490, d230050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22674 q selected
  have h2 (q : Pattern) (selected : d228491 q = 0) : d230051 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228491, d230051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228491, d230051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228492 q = 0) : d230052 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228492, d230052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228492, d230052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228494 q = 0) : d230054 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228494, d230054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228494, d230054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228499 q = 0) : d230059 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228499, d230059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228499, d230059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228500 q = 0) : d230060 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228500, d230060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228500, d230060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22677 (p : Pattern) (selected : d228506 p = 0) : d230066 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228497 q = 0) : d230057 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228497, d230057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22675 q selected
    | true =>
      simp only [d228497, d230057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228498 q = 0) : d230058 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228498, d230058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228498, d230058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228501 q = 0) : d230061 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228501, d230061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22676 q selected
    | true =>
      simp only [d228501, d230061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228502 q = 0) : d230062 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228502, d230062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228502, d230062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228503 q = 0) : d230063 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228503, d230063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228503, d230063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228504 q = 0) : d230064 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228504, d230064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228504, d230064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228505 q = 0) : d230065 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228505, d230065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228505, d230065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228506 q = 0) : d230066 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228506, d230066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228506, d230066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22678 (p : Pattern) (selected : d228510 p = 0) : d230070 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228501 q = 0) : d230061 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228501, d230061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22676 q selected
    | true =>
      simp only [d228501, d230061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228502 q = 0) : d230062 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228502, d230062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228502, d230062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228507 q = 0) : d230067 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228507, d230067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228507, d230067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228508 q = 0) : d230068 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228508, d230068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228508, d230068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228509 q = 0) : d230069 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228509, d230069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228509, d230069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228510 q = 0) : d230070 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228510, d230070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228510, d230070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22679 (p : Pattern) (selected : d228513 p = 0) : d230129 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227956 q = 0) : d229710 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227956, d229710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22565 q selected
    | true =>
      simp only [d227956, d229710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d227957 q = 0) : d229711 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227957, d229711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227957, d229711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d227958 q = 0) : d229712 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227958, d229712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227958, d229712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227959 q = 0) : d229713 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227959, d229713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227959, d229713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227795 q = 0) : d229591 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227795, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22536 q selected
    | true =>
      simp only [d227795, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d227796 q = 0) : d229592 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227796, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227796, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d227797 q = 0) : d229593 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227797, d229593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227797, d229593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d227798 q = 0) : d229594 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227798, d229594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227798, d229594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d227960 q = 0) : d229714 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d227960, d229714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d227960, d229714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228513 q = 0) : d230129 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228513, d230129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228513, d230129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22680 (p : Pattern) (selected : d228519 p = 0) : d230135 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228394 q = 0) : d230046 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228394, d230046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22608 q selected
    | true =>
      simp only [d228394, d230046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22653 q selected
  have h2 (q : Pattern) (selected : d228395 q = 0) : d230047 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228395, d230047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228395, d230047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228396 q = 0) : d230048 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228396, d230048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228396, d230048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228398 q = 0) : d230050 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228398, d230050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22653 q selected
    | true =>
      simp only [d228398, d230050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22654 q selected
  have h5 (q : Pattern) (selected : d228399 q = 0) : d230051 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228399, d230051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228399, d230051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228400 q = 0) : d230052 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228400, d230052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228400, d230052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228401 q = 0) : d230053 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228401, d230053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228401, d230053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228514 q = 0) : d230130 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228514, d230130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22679 q selected
    | true =>
      simp only [d228514, d230130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228515 q = 0) : d230131 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228515, d230131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228515, d230131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228516 q = 0) : d230132 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228516, d230132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228516, d230132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d228517 q = 0) : d230133 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228517, d230133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d228517, d230133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d228518 q = 0) : d230134 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228518, d230134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228518, d230134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d228519 q = 0) : d230135 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228519, d230135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d228519, d230135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro22681 (p : Pattern) (selected : d228525 p = 0) : d230141 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228520 q = 0) : d230136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228520, d230136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22680 q selected
    | true =>
      simp only [d228520, d230136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228521 q = 0) : d230137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228521, d230137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228521, d230137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228522 q = 0) : d230138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228522, d230138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228522, d230138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228523 q = 0) : d230139 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228523, d230139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228523, d230139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228524 q = 0) : d230140 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228524, d230140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228524, d230140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228525 q = 0) : d230141 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228525, d230141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228525, d230141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22682 (p : Pattern) (selected : d228531 p = 0) : d230147 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228442 q = 0) : d230094 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228442, d230094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22663 q selected
    | true =>
      simp only [d228442, d230094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22664 q selected
  have h2 (q : Pattern) (selected : d228443 q = 0) : d230095 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228443, d230095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228443, d230095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228444 q = 0) : d230096 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228444, d230096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228444, d230096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228445 q = 0) : d230097 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228445, d230097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228445, d230097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228452 q = 0) : d230104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228452, d230104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22665 q selected
    | true =>
      simp only [d228452, d230104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22666 q selected
  have h6 (q : Pattern) (selected : d228453 q = 0) : d230105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228453, d230105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228453, d230105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228454 q = 0) : d230106 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228454, d230106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228454, d230106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228475 q = 0) : d230127 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228475, d230127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22670 q selected
    | true =>
      simp only [d228475, d230127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22657 q selected
  have h9 (q : Pattern) (selected : d228511 q = 0) : d230071 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228511, d230071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22677 q selected
    | true =>
      simp only [d228511, d230071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22678 q selected
  have h10 (q : Pattern) (selected : d228512 q = 0) : d230128 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228512, d230128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d228512, d230128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d228526 q = 0) : d230142 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228526, d230142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22681 q selected
    | true =>
      simp only [d228526, d230142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d228527 q = 0) : d230143 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228527, d230143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d228527, d230143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d228528 q = 0) : d230144 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228528, d230144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d228528, d230144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d228529 q = 0) : d230145 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228529, d230145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228529, d230145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d228530 q = 0) : d230146 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228530, d230146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228530, d230146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d228531 q = 0) : d230147 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228531, d230147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228531, d230147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro22683 (p : Pattern) (selected : d228532 p = 0) : d230148 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228405 q = 0) : d230057 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228405, d230057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22655 q selected
    | true =>
      simp only [d228405, d230057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228406 q = 0) : d230058 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228406, d230058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228406, d230058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228409 q = 0) : d230061 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228409, d230061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22656 q selected
    | true =>
      simp only [d228409, d230061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228410 q = 0) : d230062 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228410, d230062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228410, d230062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228411 q = 0) : d230063 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228411, d230063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228411, d230063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228412 q = 0) : d230064 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228412, d230064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228412, d230064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228438 q = 0) : d230090 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228438, d230090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228438, d230090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228532 q = 0) : d230148 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228532, d230148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228532, d230148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22684 (p : Pattern) (selected : d228533 p = 0) : d230149 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228409 q = 0) : d230061 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228409, d230061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22656 q selected
    | true =>
      simp only [d228409, d230061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228410 q = 0) : d230062 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228410, d230062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228410, d230062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228415 q = 0) : d230067 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228415, d230067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228415, d230067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228416 q = 0) : d230068 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228416, d230068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228416, d230068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228440 q = 0) : d230092 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228440, d230092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228440, d230092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228533 q = 0) : d230149 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228533, d230149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228533, d230149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22685 (p : Pattern) (selected : d228538 p = 0) : d230154 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228405 q = 0) : d230057 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228405, d230057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22655 q selected
    | true =>
      simp only [d228405, d230057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228406 q = 0) : d230058 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228406, d230058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228406, d230058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228409 q = 0) : d230061 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228409, d230061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22656 q selected
    | true =>
      simp only [d228409, d230061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228410 q = 0) : d230062 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228410, d230062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228410, d230062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228411 q = 0) : d230063 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228411, d230063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228411, d230063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228446 q = 0) : d230098 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228446, d230098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228446, d230098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228447 q = 0) : d230099 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228447, d230099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228447, d230099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228538 q = 0) : d230154 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228538, d230154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228538, d230154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22686 (p : Pattern) (selected : d228539 p = 0) : d230155 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228409 q = 0) : d230061 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228409, d230061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22656 q selected
    | true =>
      simp only [d228409, d230061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228410 q = 0) : d230062 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228410, d230062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228410, d230062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228415 q = 0) : d230067 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228415, d230067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228415, d230067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228449 q = 0) : d230101 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228449, d230101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228449, d230101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228450 q = 0) : d230102 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228450, d230102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228450, d230102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228539 q = 0) : d230155 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228539, d230155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228539, d230155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22687 (p : Pattern) (selected : d228543 p = 0) : d230159 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228469 q = 0) : d230121 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228469, d230121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22669 q selected
    | true =>
      simp only [d228469, d230121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228470 q = 0) : d230122 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228470, d230122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228470, d230122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228405 q = 0) : d230057 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228405, d230057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22655 q selected
    | true =>
      simp only [d228405, d230057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228406 q = 0) : d230058 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228406, d230058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228406, d230058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228471 q = 0) : d230123 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228471, d230123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228471, d230123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228472 q = 0) : d230124 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228472, d230124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228472, d230124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228473 q = 0) : d230125 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228473, d230125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228473, d230125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228543 q = 0) : d230159 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228543, d230159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228543, d230159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22688 (p : Pattern) (selected : d228545 p = 0) : d230079 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228497 q = 0) : d230057 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228497, d230057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22675 q selected
    | true =>
      simp only [d228497, d230057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228498 q = 0) : d230058 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228498, d230058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228498, d230058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228501 q = 0) : d230061 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228501, d230061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22676 q selected
    | true =>
      simp only [d228501, d230061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228502 q = 0) : d230062 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228502, d230062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228502, d230062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228503 q = 0) : d230063 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228503, d230063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228503, d230063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228504 q = 0) : d230064 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228504, d230064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228504, d230064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228505 q = 0) : d230065 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228505, d230065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228505, d230065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228545 q = 0) : d230079 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228545, d230079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228545, d230079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22689 (p : Pattern) (selected : d228546 p = 0) : d230080 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228501 q = 0) : d230061 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228501, d230061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22676 q selected
    | true =>
      simp only [d228501, d230061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228502 q = 0) : d230062 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228502, d230062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228502, d230062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228507 q = 0) : d230067 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228507, d230067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228507, d230067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228508 q = 0) : d230068 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228508, d230068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228508, d230068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228509 q = 0) : d230069 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228509, d230069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228509, d230069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228546 q = 0) : d230080 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228546, d230080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228546, d230080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22690 (p : Pattern) (selected : d228549 p = 0) : d230162 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228520 q = 0) : d230136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228520, d230136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22680 q selected
    | true =>
      simp only [d228520, d230136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228521 q = 0) : d230137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228521, d230137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228521, d230137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228522 q = 0) : d230138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228522, d230138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228522, d230138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228523 q = 0) : d230139 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228523, d230139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228523, d230139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228524 q = 0) : d230140 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228524, d230140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228524, d230140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228549 q = 0) : d230162 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228549, d230162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228549, d230162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22691 (p : Pattern) (selected : d228555 p = 0) : d230168 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228442 q = 0) : d230094 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228442, d230094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22663 q selected
    | true =>
      simp only [d228442, d230094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22664 q selected
  have h2 (q : Pattern) (selected : d228443 q = 0) : d230095 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228443, d230095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228443, d230095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228444 q = 0) : d230096 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228444, d230096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228444, d230096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228445 q = 0) : d230097 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228445, d230097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228445, d230097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228452 q = 0) : d230104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228452, d230104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22665 q selected
    | true =>
      simp only [d228452, d230104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22666 q selected
  have h6 (q : Pattern) (selected : d228453 q = 0) : d230105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228453, d230105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228453, d230105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228454 q = 0) : d230106 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228454, d230106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228454, d230106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228475 q = 0) : d230127 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228475, d230127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22670 q selected
    | true =>
      simp only [d228475, d230127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22657 q selected
  have h9 (q : Pattern) (selected : d228511 q = 0) : d230071 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228511, d230071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22677 q selected
    | true =>
      simp only [d228511, d230071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22678 q selected
  have h10 (q : Pattern) (selected : d228512 q = 0) : d230128 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228512, d230128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d228512, d230128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d228526 q = 0) : d230142 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228526, d230142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22681 q selected
    | true =>
      simp only [d228526, d230142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d228527 q = 0) : d230143 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228527, d230143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d228527, d230143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d228528 q = 0) : d230144 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228528, d230144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d228528, d230144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d228529 q = 0) : d230145 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228529, d230145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228529, d230145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d228530 q = 0) : d230146 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228530, d230146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228530, d230146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d228534 q = 0) : d230150 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228534, d230150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22683 q selected
    | true =>
      simp only [d228534, d230150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22684 q selected
  have h17 (q : Pattern) (selected : d228535 q = 0) : d230151 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228535, d230151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228535, d230151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d228536 q = 0) : d230152 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228536, d230152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d228536, d230152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d228537 q = 0) : d230153 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228537, d230153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228537, d230153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d228540 q = 0) : d230156 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228540, d230156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22685 q selected
    | true =>
      simp only [d228540, d230156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22686 q selected
  have h21 (q : Pattern) (selected : d228541 q = 0) : d230157 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228541, d230157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228541, d230157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d228542 q = 0) : d230158 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228542, d230158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d228542, d230158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d228544 q = 0) : d230160 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228544, d230160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22687 q selected
    | true =>
      simp only [d228544, d230160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22660 q selected
  have h24 (q : Pattern) (selected : d228547 q = 0) : d230081 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228547, d230081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22688 q selected
    | true =>
      simp only [d228547, d230081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22689 q selected
  have h25 (q : Pattern) (selected : d228548 q = 0) : d230161 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228548, d230161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d228548, d230161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d228550 q = 0) : d230163 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228550, d230163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22690 q selected
    | true =>
      simp only [d228550, d230163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d228551 q = 0) : d230164 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228551, d230164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d228551, d230164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d228552 q = 0) : d230165 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228552, d230165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d228552, d230165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d228553 q = 0) : d230166 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228553, d230166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d228553, d230166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d228554 q = 0) : d230167 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228554, d230167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d228554, d230167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d228555 q = 0) : d230168 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228555, d230168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d228555, d230168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro22692 (p : Pattern) (selected : d228562 p = 0) : d230175 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228419 q = 0) : d230071 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228419, d230071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22657 q selected
    | true =>
      simp only [d228419, d230071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22658 q selected
  have h2 (q : Pattern) (selected : d228420 q = 0) : d230072 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228420, d230072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228420, d230072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228421 q = 0) : d230073 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228421, d230073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228421, d230073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228422 q = 0) : d230074 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228422, d230074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228422, d230074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228423 q = 0) : d230075 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228423, d230075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228423, d230075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228557 q = 0) : d230170 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228557, d230170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22658 q selected
    | true =>
      simp only [d228557, d230170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228558 q = 0) : d230171 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228558, d230171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228558, d230171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228559 q = 0) : d230172 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228559, d230172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228559, d230172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228560 q = 0) : d230173 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228560, d230173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228560, d230173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228561 q = 0) : d230174 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228561, d230174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228561, d230174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d228562 q = 0) : d230175 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228562, d230175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228562, d230175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22693 (p : Pattern) (selected : d228568 p = 0) : d230181 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228557 q = 0) : d230170 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228557, d230170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22658 q selected
    | true =>
      simp only [d228557, d230170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228558 q = 0) : d230171 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228558, d230171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228558, d230171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228559 q = 0) : d230172 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228559, d230172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228559, d230172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228560 q = 0) : d230173 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228560, d230173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228560, d230173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228561 q = 0) : d230174 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228561, d230174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228561, d230174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228563 q = 0) : d230176 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228563, d230176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22661 q selected
    | true =>
      simp only [d228563, d230176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228564 q = 0) : d230177 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228564, d230177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228564, d230177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228565 q = 0) : d230178 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228565, d230178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228565, d230178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228566 q = 0) : d230179 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228566, d230179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228566, d230179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228567 q = 0) : d230180 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228567, d230180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228567, d230180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d228568 q = 0) : d230181 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228568, d230181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228568, d230181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22694 (p : Pattern) (selected : d228575 p = 0) : d230188 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228544 q = 0) : d230160 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228544, d230160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22687 q selected
    | true =>
      simp only [d228544, d230160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22660 q selected
  have h2 (q : Pattern) (selected : d228547 q = 0) : d230081 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228547, d230081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22688 q selected
    | true =>
      simp only [d228547, d230081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22689 q selected
  have h3 (q : Pattern) (selected : d228548 q = 0) : d230161 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228548, d230161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228548, d230161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228550 q = 0) : d230163 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228550, d230163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22690 q selected
    | true =>
      simp only [d228550, d230163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228551 q = 0) : d230164 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228551, d230164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228551, d230164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228552 q = 0) : d230165 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228552, d230165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228552, d230165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228573 q = 0) : d230186 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228573, d230186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228573, d230186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228574 q = 0) : d230187 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228574, d230187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228574, d230187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d228575 q = 0) : d230188 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228575, d230188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228575, d230188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro22695 (p : Pattern) (selected : d228577 p = 0) : d230190 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228563 q = 0) : d230176 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228563, d230176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22661 q selected
    | true =>
      simp only [d228563, d230176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228564 q = 0) : d230177 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228564, d230177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228564, d230177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228565 q = 0) : d230178 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228565, d230178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228565, d230178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228566 q = 0) : d230179 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228566, d230179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228566, d230179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228567 q = 0) : d230180 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228567, d230180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228567, d230180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228577 q = 0) : d230190 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228577, d230190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228577, d230190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22696 (p : Pattern) (selected : d228588 p = 0) : d230201 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228583 q = 0) : d230196 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228583, d230196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228583, d230196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22667 q selected
  have h2 (q : Pattern) (selected : d228457 q = 0) : d230109 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228457, d230109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22667 q selected
    | true =>
      simp only [d228457, d230109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228584 q = 0) : d230197 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228584, d230197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228584, d230197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228458 q = 0) : d230110 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228458, d230110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228458, d230110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228585 q = 0) : d230198 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228585, d230198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228585, d230198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228586 q = 0) : d230199 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228586, d230199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228586, d230199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228287 q = 0) : d229966 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228287, d229966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228287, d229966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22607 q selected
  have h8 (q : Pattern) (selected : d228167 q = 0) : d229879 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228167, d229879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22607 q selected
    | true =>
      simp only [d228167, d229879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228288 q = 0) : d229967 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228288, d229967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228288, d229967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228168 q = 0) : d229880 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228168, d229880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d228168, d229880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d228289 q = 0) : d229968 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228289, d229968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228289, d229968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d228290 q = 0) : d229969 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228290, d229969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d228290, d229969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d228587 q = 0) : d230200 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228587, d230200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228587, d230200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d228044 q = 0) : d229775 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228044, d229775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228044, d229775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22565 q selected
  have h15 (q : Pattern) (selected : d227956 q = 0) : d229710 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227956, d229710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22565 q selected
    | true =>
      simp only [d227956, d229710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d228045 q = 0) : d229776 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228045, d229776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d228045, d229776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d227957 q = 0) : d229711 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227957, d229711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d227957, d229711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d228046 q = 0) : d229777 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228046, d229777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d228046, d229777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d228047 q = 0) : d229778 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228047, d229778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d228047, d229778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d228291 q = 0) : d229970 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228291, d229970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d228291, d229970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d228588 q = 0) : d230201 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228588, d230201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d228588, d230201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro22697 (p : Pattern) (selected : d228593 p = 0) : d230206 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228044 q = 0) : d229775 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228044, d229775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228044, d229775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22565 q selected
  have h2 (q : Pattern) (selected : d227956 q = 0) : d229710 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227956, d229710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22565 q selected
    | true =>
      simp only [d227956, d229710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228045 q = 0) : d229776 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228045, d229776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228045, d229776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227957 q = 0) : d229711 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227957, d229711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227957, d229711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228046 q = 0) : d229777 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228046, d229777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228046, d229777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228047 q = 0) : d229778 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228047, d229778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228047, d229778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d227872 q = 0) : d229645 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227872, d229645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227872, d229645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22536 q selected
  have h8 (q : Pattern) (selected : d227795 q = 0) : d229591 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227795, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22536 q selected
    | true =>
      simp only [d227795, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d227873 q = 0) : d229646 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227873, d229646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227873, d229646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227796 q = 0) : d229592 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227796, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d227796, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d227874 q = 0) : d229647 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227874, d229647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d227874, d229647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d227875 q = 0) : d229648 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227875, d229648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d227875, d229648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d228048 q = 0) : d229779 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228048, d229779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228048, d229779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d228592 q = 0) : d230205 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228592, d230205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d228592, d230205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d228593 q = 0) : d230206 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228593, d230206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d228593, d230206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22698 (p : Pattern) (selected : d228598 p = 0) : d230211 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d227872 q = 0) : d229645 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227872, d229645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227872, d229645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22536 q selected
  have h2 (q : Pattern) (selected : d227795 q = 0) : d229591 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227795, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22536 q selected
    | true =>
      simp only [d227795, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d227873 q = 0) : d229646 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227873, d229646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227873, d229646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227796 q = 0) : d229592 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227796, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227796, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d227874 q = 0) : d229647 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227874, d229647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d227874, d229647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d227875 q = 0) : d229648 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227875, d229648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d227875, d229648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228592 q = 0) : d230205 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228592, d230205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228592, d230205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228598 q = 0) : d230211 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228598, d230211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228598, d230211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22699 (p : Pattern) (selected : d228604 p = 0) : d230217 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228589 q = 0) : d230202 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228589, d230202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22696 q selected
    | true =>
      simp only [d228589, d230202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22634 q selected
  have h2 (q : Pattern) (selected : d228590 q = 0) : d230203 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228590, d230203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228590, d230203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228591 q = 0) : d230204 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228591, d230204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228591, d230204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228594 q = 0) : d230207 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228594, d230207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22634 q selected
    | true =>
      simp only [d228594, d230207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22697 q selected
  have h5 (q : Pattern) (selected : d228595 q = 0) : d230208 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228595, d230208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228595, d230208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228596 q = 0) : d230209 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228596, d230209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228596, d230209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228597 q = 0) : d230210 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228597, d230210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228597, d230210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228599 q = 0) : d230212 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228599, d230212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22697 q selected
    | true =>
      simp only [d228599, d230212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22698 q selected
  have h9 (q : Pattern) (selected : d228600 q = 0) : d230213 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228600, d230213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228600, d230213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228601 q = 0) : d230214 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228601, d230214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228601, d230214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d228602 q = 0) : d230215 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228602, d230215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228602, d230215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d228603 q = 0) : d230216 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228603, d230216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228603, d230216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d228604 q = 0) : d230217 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228604, d230217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d228604, d230217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro22700 (p : Pattern) (selected : d228609 p = 0) : d230222 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228594 q = 0) : d230207 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228594, d230207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22634 q selected
    | true =>
      simp only [d228594, d230207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22697 q selected
  have h2 (q : Pattern) (selected : d228595 q = 0) : d230208 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228595, d230208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228595, d230208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228596 q = 0) : d230209 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228596, d230209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228596, d230209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228599 q = 0) : d230212 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228599, d230212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22697 q selected
    | true =>
      simp only [d228599, d230212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22698 q selected
  have h5 (q : Pattern) (selected : d228600 q = 0) : d230213 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228600, d230213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228600, d230213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228601 q = 0) : d230214 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228601, d230214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228601, d230214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228602 q = 0) : d230215 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228602, d230215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228602, d230215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228607 q = 0) : d230220 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228607, d230220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228607, d230220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228608 q = 0) : d230221 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228608, d230221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228608, d230221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228609 q = 0) : d230222 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228609, d230222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228609, d230222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22701 (p : Pattern) (selected : d228615 p = 0) : d230228 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228605 q = 0) : d230218 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228605, d230218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22699 q selected
    | true =>
      simp only [d228605, d230218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228606 q = 0) : d230219 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228606, d230219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228606, d230219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228610 q = 0) : d230223 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228610, d230223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22700 q selected
    | true =>
      simp only [d228610, d230223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228611 q = 0) : d230224 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228611, d230224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228611, d230224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228612 q = 0) : d230225 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228612, d230225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228612, d230225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228613 q = 0) : d230226 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228613, d230226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228613, d230226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228614 q = 0) : d230227 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228614, d230227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228614, d230227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228615 q = 0) : d230228 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228615, d230228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228615, d230228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22702 (p : Pattern) (selected : d228617 p = 0) : d230230 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228599 q = 0) : d230212 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228599, d230212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22697 q selected
    | true =>
      simp only [d228599, d230212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22698 q selected
  have h2 (q : Pattern) (selected : d228600 q = 0) : d230213 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228600, d230213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228600, d230213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228601 q = 0) : d230214 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228601, d230214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228601, d230214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228607 q = 0) : d230220 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228607, d230220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228607, d230220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228616 q = 0) : d230229 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228616, d230229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228616, d230229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228617 q = 0) : d230230 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228617, d230230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228617, d230230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22703 (p : Pattern) (selected : d228623 p = 0) : d230236 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228610 q = 0) : d230223 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228610, d230223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22700 q selected
    | true =>
      simp only [d228610, d230223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228611 q = 0) : d230224 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228611, d230224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228611, d230224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228618 q = 0) : d230231 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228618, d230231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22702 q selected
    | true =>
      simp only [d228618, d230231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228619 q = 0) : d230232 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228619, d230232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228619, d230232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228620 q = 0) : d230233 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228620, d230233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228620, d230233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228621 q = 0) : d230234 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228621, d230234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228621, d230234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228622 q = 0) : d230235 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228622, d230235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228622, d230235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228623 q = 0) : d230236 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228623, d230236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228623, d230236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22704 (p : Pattern) (selected : d228630 p = 0) : d229971 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228625 q = 0) : d229966 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228625, d229966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228625, d229966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22671 q selected
  have h2 (q : Pattern) (selected : d228478 q = 0) : d229879 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228478, d229879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22671 q selected
    | true =>
      simp only [d228478, d229879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228626 q = 0) : d229967 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228626, d229967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228626, d229967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228479 q = 0) : d229880 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228479, d229880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228479, d229880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228627 q = 0) : d229968 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228627, d229968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228627, d229968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228628 q = 0) : d229969 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228628, d229969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228628, d229969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228319 q = 0) : d229775 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228319, d229775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228319, d229775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22611 q selected
  have h8 (q : Pattern) (selected : d228188 q = 0) : d229710 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228188, d229710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22611 q selected
    | true =>
      simp only [d228188, d229710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228320 q = 0) : d229776 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228320, d229776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228320, d229776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228189 q = 0) : d229711 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228189, d229711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d228189, d229711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d228321 q = 0) : d229777 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228321, d229777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228321, d229777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d228322 q = 0) : d229778 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228322, d229778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d228322, d229778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d228629 q = 0) : d229970 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228629, d229970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228629, d229970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d228063 q = 0) : d229645 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228063, d229645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228063, d229645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22569 q selected
  have h15 (q : Pattern) (selected : d227977 q = 0) : d229591 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227977, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22569 q selected
    | true =>
      simp only [d227977, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d228064 q = 0) : d229646 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228064, d229646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d228064, d229646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d227978 q = 0) : d229592 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227978, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d227978, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d228065 q = 0) : d229647 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228065, d229647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d228065, d229647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d228066 q = 0) : d229648 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228066, d229648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d228066, d229648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d228323 q = 0) : d229779 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228323, d229779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d228323, d229779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d228630 q = 0) : d229971 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228630, d229971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d228630, d229971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro22705 (p : Pattern) (selected : d228632 p = 0) : d230206 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228319 q = 0) : d229775 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228319, d229775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228319, d229775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22611 q selected
  have h2 (q : Pattern) (selected : d228188 q = 0) : d229710 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228188, d229710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22611 q selected
    | true =>
      simp only [d228188, d229710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228320 q = 0) : d229776 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228320, d229776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228320, d229776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228189 q = 0) : d229711 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228189, d229711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228189, d229711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228321 q = 0) : d229777 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228321, d229777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228321, d229777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228322 q = 0) : d229778 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228322, d229778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228322, d229778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228063 q = 0) : d229645 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228063, d229645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228063, d229645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22569 q selected
  have h8 (q : Pattern) (selected : d227977 q = 0) : d229591 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227977, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22569 q selected
    | true =>
      simp only [d227977, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228064 q = 0) : d229646 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228064, d229646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228064, d229646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227978 q = 0) : d229592 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227978, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d227978, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d228065 q = 0) : d229647 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228065, d229647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228065, d229647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d228066 q = 0) : d229648 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228066, d229648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d228066, d229648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d228323 q = 0) : d229779 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228323, d229779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228323, d229779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d228631 q = 0) : d230205 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228631, d230205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d228631, d230205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d228632 q = 0) : d230206 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228632, d230206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d228632, d230206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22706 (p : Pattern) (selected : d228636 p = 0) : d230211 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228063 q = 0) : d229645 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228063, d229645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228063, d229645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22569 q selected
  have h2 (q : Pattern) (selected : d227977 q = 0) : d229591 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227977, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22569 q selected
    | true =>
      simp only [d227977, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228064 q = 0) : d229646 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228064, d229646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228064, d229646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227978 q = 0) : d229592 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227978, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227978, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228065 q = 0) : d229647 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228065, d229647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228065, d229647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228066 q = 0) : d229648 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228066, d229648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228066, d229648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228631 q = 0) : d230205 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228631, d230205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228631, d230205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228636 q = 0) : d230211 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228636, d230211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228636, d230211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22707 (p : Pattern) (selected : d228643 p = 0) : d230222 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228633 q = 0) : d230207 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228633, d230207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22704 q selected
    | true =>
      simp only [d228633, d230207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22705 q selected
  have h2 (q : Pattern) (selected : d228634 q = 0) : d230208 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228634, d230208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228634, d230208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228635 q = 0) : d230209 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228635, d230209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228635, d230209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228637 q = 0) : d230212 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228637, d230212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22705 q selected
    | true =>
      simp only [d228637, d230212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22706 q selected
  have h5 (q : Pattern) (selected : d228638 q = 0) : d230213 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228638, d230213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228638, d230213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228639 q = 0) : d230214 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228639, d230214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228639, d230214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228640 q = 0) : d230215 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228640, d230215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228640, d230215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228641 q = 0) : d230220 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228641, d230220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228641, d230220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228642 q = 0) : d230221 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228642, d230221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228642, d230221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228643 q = 0) : d230222 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228643, d230222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228643, d230222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22708 (p : Pattern) (selected : d228647 p = 0) : d230230 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228637 q = 0) : d230212 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228637, d230212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22705 q selected
    | true =>
      simp only [d228637, d230212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22706 q selected
  have h2 (q : Pattern) (selected : d228638 q = 0) : d230213 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228638, d230213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228638, d230213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228639 q = 0) : d230214 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228639, d230214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228639, d230214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228641 q = 0) : d230220 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228641, d230220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228641, d230220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228646 q = 0) : d230229 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228646, d230229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228646, d230229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228647 q = 0) : d230230 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228647, d230230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228647, d230230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22709 (p : Pattern) (selected : d228653 p = 0) : d230236 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228644 q = 0) : d230223 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228644, d230223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22707 q selected
    | true =>
      simp only [d228644, d230223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228645 q = 0) : d230224 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228645, d230224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228645, d230224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228648 q = 0) : d230231 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228648, d230231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22708 q selected
    | true =>
      simp only [d228648, d230231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228649 q = 0) : d230232 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228649, d230232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228649, d230232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228650 q = 0) : d230233 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228650, d230233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228650, d230233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228651 q = 0) : d230234 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228651, d230234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228651, d230234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228652 q = 0) : d230235 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228652, d230235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228652, d230235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228653 q = 0) : d230236 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228653, d230236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228653, d230236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22710 (p : Pattern) (selected : d228657 p = 0) : d230241 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228648 q = 0) : d230231 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228648, d230231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22708 q selected
    | true =>
      simp only [d228648, d230231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228649 q = 0) : d230232 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228649, d230232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228649, d230232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228654 q = 0) : d230238 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228654, d230238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228654, d230238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228655 q = 0) : d230239 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228655, d230239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228655, d230239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228656 q = 0) : d230240 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228656, d230240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228656, d230240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228657 q = 0) : d230241 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228657, d230241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228657, d230241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22711 (p : Pattern) (selected : d228660 p = 0) : d230244 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228044 q = 0) : d229775 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228044, d229775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228044, d229775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22565 q selected
  have h2 (q : Pattern) (selected : d227956 q = 0) : d229710 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227956, d229710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22565 q selected
    | true =>
      simp only [d227956, d229710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228045 q = 0) : d229776 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228045, d229776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228045, d229776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d227957 q = 0) : d229711 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227957, d229711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d227957, d229711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228046 q = 0) : d229777 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228046, d229777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228046, d229777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228047 q = 0) : d229778 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228047, d229778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228047, d229778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d227872 q = 0) : d229645 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227872, d229645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d227872, d229645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22536 q selected
  have h8 (q : Pattern) (selected : d227795 q = 0) : d229591 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d227795, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22536 q selected
    | true =>
      simp only [d227795, d229591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d227873 q = 0) : d229646 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227873, d229646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d227873, d229646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d227796 q = 0) : d229592 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227796, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d227796, d229592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d227874 q = 0) : d229647 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d227874, d229647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d227874, d229647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d227875 q = 0) : d229648 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d227875, d229648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d227875, d229648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d228048 q = 0) : d229779 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228048, d229779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228048, d229779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d228660 q = 0) : d230244 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228660, d230244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d228660, d230244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h14 p selected
theorem eqIntro22712 (p : Pattern) (selected : d228666 p = 0) : d230250 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228594 q = 0) : d230207 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228594, d230207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22634 q selected
    | true =>
      simp only [d228594, d230207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22697 q selected
  have h2 (q : Pattern) (selected : d228595 q = 0) : d230208 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228595, d230208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228595, d230208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228596 q = 0) : d230209 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228596, d230209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228596, d230209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228599 q = 0) : d230212 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228599, d230212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22697 q selected
    | true =>
      simp only [d228599, d230212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22698 q selected
  have h5 (q : Pattern) (selected : d228600 q = 0) : d230213 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228600, d230213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228600, d230213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228601 q = 0) : d230214 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228601, d230214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228601, d230214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228602 q = 0) : d230215 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228602, d230215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228602, d230215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228661 q = 0) : d230245 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228661, d230245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22711 q selected
    | true =>
      simp only [d228661, d230245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228662 q = 0) : d230246 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228662, d230246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228662, d230246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228663 q = 0) : d230247 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228663, d230247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228663, d230247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d228664 q = 0) : d230248 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228664, d230248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d228664, d230248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d228665 q = 0) : d230249 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228665, d230249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228665, d230249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d228666 q = 0) : d230250 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228666, d230250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d228666, d230250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro22713 (p : Pattern) (selected : d228672 p = 0) : d230256 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228667 q = 0) : d230251 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228667, d230251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22712 q selected
    | true =>
      simp only [d228667, d230251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228668 q = 0) : d230252 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228668, d230252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228668, d230252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228669 q = 0) : d230253 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228669, d230253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228669, d230253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228670 q = 0) : d230254 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228670, d230254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228670, d230254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228671 q = 0) : d230255 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228671, d230255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228671, d230255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228672 q = 0) : d230256 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228672, d230256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228672, d230256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22714 (p : Pattern) (selected : d228678 p = 0) : d230262 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228624 q = 0) : d230237 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228624, d230237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22701 q selected
    | true =>
      simp only [d228624, d230237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22703 q selected
  have h2 (q : Pattern) (selected : d228658 q = 0) : d230242 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228658, d230242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22709 q selected
    | true =>
      simp only [d228658, d230242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22710 q selected
  have h3 (q : Pattern) (selected : d228659 q = 0) : d230243 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228659, d230243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228659, d230243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228673 q = 0) : d230257 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228673, d230257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22713 q selected
    | true =>
      simp only [d228673, d230257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228674 q = 0) : d230258 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228674, d230258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228674, d230258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228675 q = 0) : d230259 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228675, d230259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228675, d230259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228676 q = 0) : d230260 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228676, d230260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228676, d230260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228677 q = 0) : d230261 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228677, d230261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228677, d230261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d228678 q = 0) : d230262 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228678, d230262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228678, d230262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro22715 (p : Pattern) (selected : d228683 p = 0) : d230241 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228618 q = 0) : d230231 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228618, d230231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22702 q selected
    | true =>
      simp only [d228618, d230231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228619 q = 0) : d230232 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228619, d230232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228619, d230232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228680 q = 0) : d230238 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228680, d230238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228680, d230238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228681 q = 0) : d230239 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228681, d230239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228681, d230239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228682 q = 0) : d230240 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228682, d230240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228682, d230240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228683 q = 0) : d230241 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228683, d230241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228683, d230241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22716 (p : Pattern) (selected : d228689 p = 0) : d230269 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228684 q = 0) : d230264 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228684, d230264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22715 q selected
    | true =>
      simp only [d228684, d230264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228685 q = 0) : d230265 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228685, d230265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228685, d230265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228686 q = 0) : d230266 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228686, d230266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228686, d230266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228687 q = 0) : d230267 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228687, d230267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228687, d230267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228688 q = 0) : d230268 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228688, d230268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228688, d230268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228689 q = 0) : d230269 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228689, d230269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228689, d230269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22717 (p : Pattern) (selected : d228695 p = 0) : d230275 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228425 q = 0) : d230077 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228425, d230077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228425, d230077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22659 q selected
  have h2 (q : Pattern) (selected : d228426 q = 0) : d230078 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d228426, d230078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228426, d230078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228435 q = 0) : d230087 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228435, d230087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22659 q selected
    | true =>
      simp only [d228435, d230087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22662 q selected
  have h4 (q : Pattern) (selected : d228436 q = 0) : d230088 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d228436, d230088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228436, d230088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228437 q = 0) : d230089 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d228437, d230089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228437, d230089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228556 q = 0) : d230169 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228556, d230169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22682 q selected
    | true =>
      simp only [d228556, d230169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22691 q selected
  have h7 (q : Pattern) (selected : d228569 q = 0) : d230182 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228569, d230182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22692 q selected
    | true =>
      simp only [d228569, d230182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22693 q selected
  have h8 (q : Pattern) (selected : d228570 q = 0) : d230183 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d228570, d230183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228570, d230183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d228571 q = 0) : d230184 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d228571, d230184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d228571, d230184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d228572 q = 0) : d230185 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d228572, d230185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228572, d230185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d228576 q = 0) : d230189 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228576, d230189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228576, d230189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22694 q selected
  have h12 (q : Pattern) (selected : d228578 q = 0) : d230191 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228578, d230191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228578, d230191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22695 q selected
  have h13 (q : Pattern) (selected : d228579 q = 0) : d230192 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d228579, d230192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d228579, d230192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d228580 q = 0) : d230193 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d228580, d230193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d228580, d230193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d228581 q = 0) : d230194 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d228581, d230194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d228581, d230194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d228582 q = 0) : d230195 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d228582, d230195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d228582, d230195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d228679 q = 0) : d230263 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228679, d230263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228679, d230263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22714 q selected
  have h18 (q : Pattern) (selected : d228690 q = 0) : d230270 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d228690, d230270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228690, d230270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22716 q selected
  have h19 (q : Pattern) (selected : d228691 q = 0) : d230271 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d228691, d230271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d228691, d230271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d228692 q = 0) : d230272 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d228692, d230272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d228692, d230272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d228693 q = 0) : d230273 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d228693, d230273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d228693, d230273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d228694 q = 0) : d230274 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d228694, d230274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d228694, d230274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d228695 q = 0) : d230275 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d228695, d230275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d228695, d230275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro22718 (p : Pattern) (selected : d228701 p = 0) : d230281 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228696 q = 0) : d230276 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d228696, d230276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228696, d230276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22717 q selected
  have h2 (q : Pattern) (selected : d228697 q = 0) : d230277 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d228697, d230277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228697, d230277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228698 q = 0) : d230278 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d228698, d230278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228698, d230278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228699 q = 0) : d230279 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d228699, d230279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228699, d230279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228700 q = 0) : d230280 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d228700, d230280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228700, d230280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228701 q = 0) : d230281 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d228701, d230281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228701, d230281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22719 (p : Pattern) (selected : d228707 p = 0) : d230287 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1204 q = 0) : d52785 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1204, d52785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro406 q selected
    | true =>
      simp only [d1204, d52785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1205 q = 0) : d52786 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1205, d52786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1205, d52786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1534 q = 0) : d52975 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1534, d52975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro462 q selected
    | true =>
      simp only [d1534, d52975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1535 q = 0) : d52976 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1535, d52976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1535, d52976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1536 q = 0) : d52977 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1536, d52977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1536, d52977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228705 q = 0) : d230285 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d228705, d230285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228705, d230285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1549 q = 0) : d52990 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1549, d52990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro465 q selected
    | true =>
      simp only [d1549, d52990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d1550 q = 0) : d52991 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1550, d52991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1550, d52991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1551 q = 0) : d52992 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1551, d52992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1551, d52992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228706 q = 0) : d230286 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d228706, d230286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228706, d230286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d228707 q = 0) : d230287 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d228707, d230287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228707, d230287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22720 (p : Pattern) (selected : d228713 p = 0) : d230293 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1534 q = 0) : d52975 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1534, d52975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro462 q selected
    | true =>
      simp only [d1534, d52975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1535 q = 0) : d52976 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1535, d52976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1535, d52976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1549 q = 0) : d52990 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1549, d52990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro465 q selected
    | true =>
      simp only [d1549, d52990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1550 q = 0) : d52991 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1550, d52991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1550, d52991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1551 q = 0) : d52992 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1551, d52992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1551, d52992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228706 q = 0) : d230286 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d228706, d230286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228706, d230286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1564 q = 0) : d53005 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro468 q selected
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d1565 q = 0) : d53006 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1566 q = 0) : d53007 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1566, d53007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1566, d53007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228712 q = 0) : d230292 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d228712, d230292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228712, d230292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d228713 q = 0) : d230293 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d228713, d230293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228713, d230293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22721 (p : Pattern) (selected : d228720 p = 0) : d230300 p = 1 := by
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
  have h5 (q : Pattern) (selected : d1566 q = 0) : d53007 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1566, d53007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1566, d53007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228712 q = 0) : d230292 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d228712, d230292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228712, d230292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1578 q = 0) : d53019 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1578, d53019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1578, d53019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228719 q = 0) : d230299 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d228719, d230299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228719, d230299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228720 q = 0) : d230300 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d228720, d230300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228720, d230300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro22722 (p : Pattern) (selected : d228726 p = 0) : d230306 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228708 q = 0) : d230288 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228708, d230288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22719 q selected
    | true =>
      simp only [d228708, d230288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228709 q = 0) : d230289 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228709, d230289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228709, d230289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228710 q = 0) : d230290 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228710, d230290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228710, d230290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228711 q = 0) : d230291 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228711, d230291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228711, d230291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228714 q = 0) : d230294 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228714, d230294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22720 q selected
    | true =>
      simp only [d228714, d230294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228715 q = 0) : d230295 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228715, d230295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228715, d230295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228716 q = 0) : d230296 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228716, d230296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228716, d230296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228717 q = 0) : d230297 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228717, d230297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228717, d230297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228718 q = 0) : d230298 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228718, d230298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228718, d230298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228721 q = 0) : d230301 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228721, d230301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22721 q selected
    | true =>
      simp only [d228721, d230301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d228722 q = 0) : d230302 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228722, d230302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d228722, d230302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d228723 q = 0) : d230303 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228723, d230303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228723, d230303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d228724 q = 0) : d230304 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228724, d230304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d228724, d230304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d228725 q = 0) : d230305 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228725, d230305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d228725, d230305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d228726 q = 0) : d230306 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228726, d230306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228726, d230306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22723 (p : Pattern) (selected : d228728 p = 0) : d230308 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228714 q = 0) : d230294 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228714, d230294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22720 q selected
    | true =>
      simp only [d228714, d230294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228715 q = 0) : d230295 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228715, d230295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228715, d230295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228716 q = 0) : d230296 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228716, d230296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228716, d230296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228717 q = 0) : d230297 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228717, d230297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228717, d230297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228721 q = 0) : d230301 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228721, d230301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22721 q selected
    | true =>
      simp only [d228721, d230301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228722 q = 0) : d230302 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228722, d230302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228722, d230302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228723 q = 0) : d230303 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228723, d230303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228723, d230303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228724 q = 0) : d230304 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228724, d230304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228724, d230304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228725 q = 0) : d230305 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228725, d230305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228725, d230305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228727 q = 0) : d230307 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228727, d230307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d228727, d230307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d228728 q = 0) : d230308 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228728, d230308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228728, d230308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22724 (p : Pattern) (selected : d228732 p = 0) : d230312 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228721 q = 0) : d230301 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228721, d230301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22721 q selected
    | true =>
      simp only [d228721, d230301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228722 q = 0) : d230302 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228722, d230302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228722, d230302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228723 q = 0) : d230303 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228723, d230303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228723, d230303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228724 q = 0) : d230304 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228724, d230304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228724, d230304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228727 q = 0) : d230307 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228727, d230307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228727, d230307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228732 q = 0) : d230312 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228732, d230312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228732, d230312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22725 (p : Pattern) (selected : d228739 p = 0) : d230319 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228729 q = 0) : d230309 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228729, d230309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22722 q selected
    | true =>
      simp only [d228729, d230309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22723 q selected
  have h2 (q : Pattern) (selected : d228730 q = 0) : d230310 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228730, d230310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228730, d230310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228731 q = 0) : d230311 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228731, d230311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228731, d230311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228733 q = 0) : d230313 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228733, d230313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22723 q selected
    | true =>
      simp only [d228733, d230313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22724 q selected
  have h5 (q : Pattern) (selected : d228734 q = 0) : d230314 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228734, d230314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228734, d230314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228735 q = 0) : d230315 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228735, d230315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228735, d230315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228736 q = 0) : d230316 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228736, d230316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228736, d230316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228737 q = 0) : d230317 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228737, d230317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228737, d230317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228738 q = 0) : d230318 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228738, d230318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228738, d230318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228739 q = 0) : d230319 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228739, d230319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228739, d230319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22726 (p : Pattern) (selected : d228743 p = 0) : d230323 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228733 q = 0) : d230313 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228733, d230313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22723 q selected
    | true =>
      simp only [d228733, d230313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22724 q selected
  have h2 (q : Pattern) (selected : d228734 q = 0) : d230314 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228734, d230314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228734, d230314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228735 q = 0) : d230315 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228735, d230315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228735, d230315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228737 q = 0) : d230317 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228737, d230317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228737, d230317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228742 q = 0) : d230322 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228742, d230322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228742, d230322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228743 q = 0) : d230323 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228743, d230323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228743, d230323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22727 (p : Pattern) (selected : d228749 p = 0) : d230329 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228740 q = 0) : d230320 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228740, d230320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22725 q selected
    | true =>
      simp only [d228740, d230320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228741 q = 0) : d230321 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228741, d230321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228741, d230321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228744 q = 0) : d230324 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228744, d230324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22726 q selected
    | true =>
      simp only [d228744, d230324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228745 q = 0) : d230325 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228745, d230325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228745, d230325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228746 q = 0) : d230326 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228746, d230326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228746, d230326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228747 q = 0) : d230327 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228747, d230327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228747, d230327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228748 q = 0) : d230328 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228748, d230328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228748, d230328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228749 q = 0) : d230329 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228749, d230329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228749, d230329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22728 (p : Pattern) (selected : d228753 p = 0) : d230333 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228744 q = 0) : d230324 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228744, d230324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22726 q selected
    | true =>
      simp only [d228744, d230324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228745 q = 0) : d230325 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228745, d230325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228745, d230325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228750 q = 0) : d230330 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228750, d230330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228750, d230330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228751 q = 0) : d230331 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228751, d230331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228751, d230331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228752 q = 0) : d230332 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228752, d230332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228752, d230332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228753 q = 0) : d230333 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228753, d230333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228753, d230333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22729 (p : Pattern) (selected : d228759 p = 0) : d230339 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228754 q = 0) : d230334 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228754, d230334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22727 q selected
    | true =>
      simp only [d228754, d230334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22728 q selected
  have h2 (q : Pattern) (selected : d228755 q = 0) : d230335 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228755, d230335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228755, d230335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228756 q = 0) : d230336 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228756, d230336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228756, d230336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228757 q = 0) : d230337 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228757, d230337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228757, d230337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228758 q = 0) : d230338 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228758, d230338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228758, d230338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228759 q = 0) : d230339 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228759, d230339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228759, d230339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22730 (p : Pattern) (selected : d228762 p = 0) : d230342 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228740 q = 0) : d230320 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228740, d230320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22725 q selected
    | true =>
      simp only [d228740, d230320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228741 q = 0) : d230321 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228741, d230321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228741, d230321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228744 q = 0) : d230324 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228744, d230324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22726 q selected
    | true =>
      simp only [d228744, d230324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228745 q = 0) : d230325 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228745, d230325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228745, d230325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228746 q = 0) : d230326 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228746, d230326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228746, d230326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228747 q = 0) : d230327 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228747, d230327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228747, d230327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228748 q = 0) : d230328 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228748, d230328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228748, d230328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228762 q = 0) : d230342 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228762, d230342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228762, d230342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro22731 (p : Pattern) (selected : d228763 p = 0) : d230343 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228744 q = 0) : d230324 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228744, d230324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22726 q selected
    | true =>
      simp only [d228744, d230324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228745 q = 0) : d230325 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228745, d230325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228745, d230325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228750 q = 0) : d230330 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228750, d230330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228750, d230330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228751 q = 0) : d230331 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228751, d230331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228751, d230331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228752 q = 0) : d230332 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228752, d230332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228752, d230332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228763 q = 0) : d230343 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228763, d230343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228763, d230343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22732 (p : Pattern) (selected : d228769 p = 0) : d230349 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228754 q = 0) : d230334 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228754, d230334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22727 q selected
    | true =>
      simp only [d228754, d230334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22728 q selected
  have h2 (q : Pattern) (selected : d228755 q = 0) : d230335 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228755, d230335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228755, d230335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228756 q = 0) : d230336 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228756, d230336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228756, d230336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228757 q = 0) : d230337 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228757, d230337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228757, d230337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228758 q = 0) : d230338 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228758, d230338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228758, d230338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228764 q = 0) : d230344 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d228764, d230344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22730 q selected
    | true =>
      simp only [d228764, d230344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22731 q selected
  have h7 (q : Pattern) (selected : d228765 q = 0) : d230345 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d228765, d230345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228765, d230345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228766 q = 0) : d230346 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d228766, d230346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228766, d230346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228767 q = 0) : d230347 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d228767, d230347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228767, d230347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228768 q = 0) : d230348 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d228768, d230348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228768, d230348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d228769 q = 0) : d230349 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d228769, d230349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228769, d230349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22733 (p : Pattern) (selected : d228774 p = 0) : d230354 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228740 q = 0) : d230320 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228740, d230320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22725 q selected
    | true =>
      simp only [d228740, d230320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228741 q = 0) : d230321 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228741, d230321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228741, d230321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228744 q = 0) : d230324 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228744, d230324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22726 q selected
    | true =>
      simp only [d228744, d230324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228745 q = 0) : d230325 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228745, d230325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228745, d230325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228746 q = 0) : d230326 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228746, d230326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228746, d230326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228747 q = 0) : d230327 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228747, d230327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228747, d230327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228773 q = 0) : d230353 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228773, d230353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228773, d230353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228774 q = 0) : d230354 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228774, d230354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228774, d230354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22734 (p : Pattern) (selected : d228776 p = 0) : d230356 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228744 q = 0) : d230324 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228744, d230324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22726 q selected
    | true =>
      simp only [d228744, d230324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228745 q = 0) : d230325 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228745, d230325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228745, d230325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228750 q = 0) : d230330 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228750, d230330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228750, d230330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228751 q = 0) : d230331 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228751, d230331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228751, d230331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228775 q = 0) : d230355 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228775, d230355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228775, d230355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228776 q = 0) : d230356 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228776, d230356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228776, d230356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22735 (p : Pattern) (selected : d228783 p = 0) : d230363 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228740 q = 0) : d230320 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228740, d230320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22725 q selected
    | true =>
      simp only [d228740, d230320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228741 q = 0) : d230321 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228741, d230321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228741, d230321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228744 q = 0) : d230324 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228744, d230324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22726 q selected
    | true =>
      simp only [d228744, d230324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228745 q = 0) : d230325 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228745, d230325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228745, d230325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228746 q = 0) : d230326 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228746, d230326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228746, d230326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228781 q = 0) : d230361 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228781, d230361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228781, d230361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228782 q = 0) : d230362 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228782, d230362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228782, d230362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228783 q = 0) : d230363 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228783, d230363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228783, d230363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22736 (p : Pattern) (selected : d228786 p = 0) : d230366 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228744 q = 0) : d230324 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228744, d230324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22726 q selected
    | true =>
      simp only [d228744, d230324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228745 q = 0) : d230325 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228745, d230325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228745, d230325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228750 q = 0) : d230330 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228750, d230330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228750, d230330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228784 q = 0) : d230364 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228784, d230364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228784, d230364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228785 q = 0) : d230365 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228785, d230365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228785, d230365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228786 q = 0) : d230366 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228786, d230366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228786, d230366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro22737 (p : Pattern) (selected : d228791 p = 0) : d230371 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1204 q = 0) : d52785 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1204, d52785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro406 q selected
    | true =>
      simp only [d1204, d52785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1205 q = 0) : d52786 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1205, d52786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1205, d52786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1661 q = 0) : d53102 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1661, d53102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1661, d53102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228790 q = 0) : d230370 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d228790, d230370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228790, d230370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1534 q = 0) : d52975 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1534, d52975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro462 q selected
    | true =>
      simp only [d1534, d52975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d1535 q = 0) : d52976 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1535, d52976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1535, d52976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1536 q = 0) : d52977 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1536, d52977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1536, d52977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228705 q = 0) : d230285 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d228705, d230285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228705, d230285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228791 q = 0) : d230371 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d228791, d230371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228791, d230371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro22738 (p : Pattern) (selected : d228797 p = 0) : d230377 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228792 q = 0) : d230372 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228792, d230372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22737 q selected
    | true =>
      simp only [d228792, d230372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228793 q = 0) : d230373 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228793, d230373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228793, d230373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228794 q = 0) : d230374 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228794, d230374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228794, d230374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228795 q = 0) : d230375 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228795, d230375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228795, d230375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228708 q = 0) : d230288 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228708, d230288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22719 q selected
    | true =>
      simp only [d228708, d230288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228709 q = 0) : d230289 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228709, d230289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228709, d230289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228710 q = 0) : d230290 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228710, d230290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228710, d230290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228711 q = 0) : d230291 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228711, d230291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228711, d230291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228796 q = 0) : d230376 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228796, d230376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228796, d230376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228714 q = 0) : d230294 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228714, d230294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22720 q selected
    | true =>
      simp only [d228714, d230294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d228715 q = 0) : d230295 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228715, d230295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d228715, d230295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d228716 q = 0) : d230296 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228716, d230296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228716, d230296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d228717 q = 0) : d230297 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228717, d230297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d228717, d230297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d228718 q = 0) : d230298 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228718, d230298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d228718, d230298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d228797 q = 0) : d230377 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228797, d230377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228797, d230377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22739 (p : Pattern) (selected : d228803 p = 0) : d230383 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228798 q = 0) : d230378 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228798, d230378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22738 q selected
    | true =>
      simp only [d228798, d230378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22722 q selected
  have h2 (q : Pattern) (selected : d228799 q = 0) : d230379 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228799, d230379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228799, d230379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228800 q = 0) : d230380 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228800, d230380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228800, d230380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228729 q = 0) : d230309 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228729, d230309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22722 q selected
    | true =>
      simp only [d228729, d230309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22723 q selected
  have h5 (q : Pattern) (selected : d228730 q = 0) : d230310 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228730, d230310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228730, d230310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228731 q = 0) : d230311 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228731, d230311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228731, d230311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228801 q = 0) : d230381 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228801, d230381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228801, d230381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228733 q = 0) : d230313 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228733, d230313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22723 q selected
    | true =>
      simp only [d228733, d230313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22724 q selected
  have h9 (q : Pattern) (selected : d228734 q = 0) : d230314 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228734, d230314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228734, d230314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228735 q = 0) : d230315 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228735, d230315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228735, d230315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d228736 q = 0) : d230316 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228736, d230316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228736, d230316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d228802 q = 0) : d230382 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228802, d230382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228802, d230382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d228803 q = 0) : d230383 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228803, d230383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d228803, d230383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro22740 (p : Pattern) (selected : d228809 p = 0) : d230389 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228804 q = 0) : d230384 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228804, d230384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22739 q selected
    | true =>
      simp only [d228804, d230384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228805 q = 0) : d230385 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228805, d230385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228805, d230385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228740 q = 0) : d230320 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228740, d230320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22725 q selected
    | true =>
      simp only [d228740, d230320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228741 q = 0) : d230321 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228741, d230321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228741, d230321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228806 q = 0) : d230386 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228806, d230386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228806, d230386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228807 q = 0) : d230387 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228807, d230387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228807, d230387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228808 q = 0) : d230388 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228808, d230388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228808, d230388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228809 q = 0) : d230389 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228809, d230389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228809, d230389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro22741 (p : Pattern) (selected : d228813 p = 0) : d230287 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1700 q = 0) : d52785 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1700, d52785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro494 q selected
    | true =>
      simp only [d1700, d52785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1701 q = 0) : d52786 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1701, d52786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1701, d52786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1705 q = 0) : d52975 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1705, d52975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro495 q selected
    | true =>
      simp only [d1705, d52975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1706 q = 0) : d52976 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1706, d52976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1706, d52976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1707 q = 0) : d52977 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1707, d52977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1707, d52977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228811 q = 0) : d230285 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d228811, d230285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228811, d230285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1720 q = 0) : d52990 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1720, d52990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro498 q selected
    | true =>
      simp only [d1720, d52990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d1721 q = 0) : d52991 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1721, d52991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1721, d52991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1722 q = 0) : d52992 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1722, d52992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1722, d52992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228812 q = 0) : d230286 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d228812, d230286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228812, d230286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d228813 q = 0) : d230287 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d228813, d230287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228813, d230287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22742 (p : Pattern) (selected : d228819 p = 0) : d230293 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1705 q = 0) : d52975 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1705, d52975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro495 q selected
    | true =>
      simp only [d1705, d52975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1706 q = 0) : d52976 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1706, d52976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1706, d52976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1720 q = 0) : d52990 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1720, d52990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro498 q selected
    | true =>
      simp only [d1720, d52990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1721 q = 0) : d52991 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1721, d52991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1721, d52991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1722 q = 0) : d52992 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1722, d52992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1722, d52992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228812 q = 0) : d230286 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d228812, d230286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228812, d230286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1735 q = 0) : d53005 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1735, d53005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro501 q selected
    | true =>
      simp only [d1735, d53005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d1736 q = 0) : d53006 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1736, d53006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1736, d53006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1737 q = 0) : d53007 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1737, d53007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1737, d53007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228818 q = 0) : d230292 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d228818, d230292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228818, d230292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d228819 q = 0) : d230293 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d228819, d230293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228819, d230293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22743 (p : Pattern) (selected : d228826 p = 0) : d230300 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1720 q = 0) : d52990 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1720, d52990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro498 q selected
    | true =>
      simp only [d1720, d52990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1721 q = 0) : d52991 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1721, d52991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1721, d52991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h5 (q : Pattern) (selected : d1737 q = 0) : d53007 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1737, d53007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1737, d53007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228818 q = 0) : d230292 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d228818, d230292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228818, d230292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1749 q = 0) : d53019 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1749, d53019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1749, d53019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228825 q = 0) : d230299 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d228825, d230299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228825, d230299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228826 q = 0) : d230300 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d228826, d230300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228826, d230300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro22744 (p : Pattern) (selected : d228832 p = 0) : d230306 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228814 q = 0) : d230288 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228814, d230288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22741 q selected
    | true =>
      simp only [d228814, d230288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228815 q = 0) : d230289 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228815, d230289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228815, d230289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228816 q = 0) : d230290 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228816, d230290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228816, d230290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228817 q = 0) : d230291 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228817, d230291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228817, d230291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228820 q = 0) : d230294 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228820, d230294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22742 q selected
    | true =>
      simp only [d228820, d230294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228821 q = 0) : d230295 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228821, d230295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228821, d230295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228822 q = 0) : d230296 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228822, d230296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228822, d230296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228823 q = 0) : d230297 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228823, d230297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228823, d230297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228824 q = 0) : d230298 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228824, d230298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228824, d230298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228827 q = 0) : d230301 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228827, d230301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22743 q selected
    | true =>
      simp only [d228827, d230301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d228828 q = 0) : d230302 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228828, d230302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d228828, d230302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d228829 q = 0) : d230303 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228829, d230303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228829, d230303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d228830 q = 0) : d230304 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228830, d230304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d228830, d230304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d228831 q = 0) : d230305 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228831, d230305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d228831, d230305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d228832 q = 0) : d230306 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228832, d230306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228832, d230306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro22745 (p : Pattern) (selected : d228834 p = 0) : d230308 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228820 q = 0) : d230294 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228820, d230294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22742 q selected
    | true =>
      simp only [d228820, d230294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228821 q = 0) : d230295 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228821, d230295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228821, d230295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228822 q = 0) : d230296 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228822, d230296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228822, d230296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228823 q = 0) : d230297 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228823, d230297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228823, d230297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228827 q = 0) : d230301 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228827, d230301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22743 q selected
    | true =>
      simp only [d228827, d230301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228828 q = 0) : d230302 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228828, d230302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228828, d230302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228829 q = 0) : d230303 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228829, d230303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228829, d230303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228830 q = 0) : d230304 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228830, d230304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228830, d230304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228831 q = 0) : d230305 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228831, d230305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228831, d230305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228833 q = 0) : d230307 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228833, d230307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d228833, d230307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d228834 q = 0) : d230308 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228834, d230308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228834, d230308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro22746 (p : Pattern) (selected : d228838 p = 0) : d230312 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228827 q = 0) : d230301 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d228827, d230301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22743 q selected
    | true =>
      simp only [d228827, d230301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228828 q = 0) : d230302 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d228828, d230302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d228828, d230302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d228829 q = 0) : d230303 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228829, d230303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228829, d230303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228830 q = 0) : d230304 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d228830, d230304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228830, d230304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228833 q = 0) : d230307 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d228833, d230307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228833, d230307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228838 q = 0) : d230312 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d228838, d230312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228838, d230312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22747 (p : Pattern) (selected : d228845 p = 0) : d230319 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228835 q = 0) : d230309 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228835, d230309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22744 q selected
    | true =>
      simp only [d228835, d230309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22745 q selected
  have h2 (q : Pattern) (selected : d228836 q = 0) : d230310 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228836, d230310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228836, d230310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228837 q = 0) : d230311 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228837, d230311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228837, d230311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228839 q = 0) : d230313 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228839, d230313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22745 q selected
    | true =>
      simp only [d228839, d230313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22746 q selected
  have h5 (q : Pattern) (selected : d228840 q = 0) : d230314 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228840, d230314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228840, d230314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228841 q = 0) : d230315 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228841, d230315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228841, d230315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d228842 q = 0) : d230316 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228842, d230316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228842, d230316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d228843 q = 0) : d230317 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228843, d230317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228843, d230317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d228844 q = 0) : d230318 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228844, d230318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d228844, d230318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d228845 q = 0) : d230319 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228845, d230319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d228845, d230319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro22748 (p : Pattern) (selected : d228849 p = 0) : d230323 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228839 q = 0) : d230313 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d228839, d230313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22745 q selected
    | true =>
      simp only [d228839, d230313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22746 q selected
  have h2 (q : Pattern) (selected : d228840 q = 0) : d230314 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d228840, d230314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228840, d230314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228841 q = 0) : d230315 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d228841, d230315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228841, d230315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d228843 q = 0) : d230317 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d228843, d230317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228843, d230317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228848 q = 0) : d230322 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d228848, d230322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d228848, d230322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d228849 q = 0) : d230323 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d228849, d230323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228849, d230323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro22749 (p : Pattern) (selected : d228855 p = 0) : d230329 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d228846 q = 0) : d230320 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228846, d230320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22747 q selected
    | true =>
      simp only [d228846, d230320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d228847 q = 0) : d230321 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228847, d230321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228847, d230321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d228850 q = 0) : d230324 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d228850, d230324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22748 q selected
    | true =>
      simp only [d228850, d230324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d228851 q = 0) : d230325 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d228851, d230325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228851, d230325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d228852 q = 0) : d230326 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d228852, d230326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d228852, d230326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d228853 q = 0) : d230327 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d228853, d230327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d228853, d230327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d228854 q = 0) : d230328 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d228854, d230328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d228854, d230328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d228855 q = 0) : d230329 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d228855, d230329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d228855, d230329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
end NetHack.Soko22Hazard87
