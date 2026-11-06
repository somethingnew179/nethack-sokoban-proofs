import NetHack.Soko22Hazard87.EqIntroBlocks0159
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro40000 (p : Pattern) (selected : d47563 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d96 q = 2) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro657 q selected
  have h2 (q : Pattern) (selected : d97 q = 2) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d98 q = 2) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d99 q = 2) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d47562 q = 2) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d47562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47563 q = 2) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d47563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro40001 (p : Pattern) (selected : d47569 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47564 q = 2) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d47564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro40000 q selected
    | true =>
      simp only [d47564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47565 q = 2) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d47565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47566 q = 2) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d47566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47567 q = 2) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d47567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47568 q = 2) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d47568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47569 q = 2) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d47569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro40002 (p : Pattern) (selected : d47575 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47570 q = 2) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d47570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro40001 q selected
    | true =>
      simp only [d47570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47571 q = 2) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d47571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47572 q = 2) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d47572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47573 q = 2) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d47573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47574 q = 2) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d47574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47575 q = 2) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d47575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro40003 (p : Pattern) (selected : d47581 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47576 q = 2) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d47576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro40002 q selected
    | true =>
      simp only [d47576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47577 q = 2) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d47577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47578 q = 2) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d47578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47579 q = 2) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d47579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47580 q = 2) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d47580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47581 q = 2) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d47581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro40004 (p : Pattern) (selected : d47587 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47582 q = 2) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d47582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro40003 q selected
    | true =>
      simp only [d47582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47583 q = 2) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d47583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47584 q = 2) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d47584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47585 q = 2) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d47585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47586 q = 2) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d47586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47587 q = 2) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d47587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro40005 (p : Pattern) (selected : d47593 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47588 q = 2) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d47588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro40004 q selected
    | true =>
      simp only [d47588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47589 q = 2) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d47589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47590 q = 2) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d47590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47591 q = 2) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d47591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47592 q = 2) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d47592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47593 q = 2) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d47593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro40006 (p : Pattern) (selected : d47599 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47594 q = 2) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d47594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro40005 q selected
    | true =>
      simp only [d47594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47595 q = 2) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d47595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47596 q = 2) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d47596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47597 q = 2) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d47597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47598 q = 2) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d47598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47599 q = 2) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d47599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro40007 (p : Pattern) (selected : d47605 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47600 q = 2) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d47600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro40006 q selected
    | true =>
      simp only [d47600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47601 q = 2) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d47601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47602 q = 2) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d47602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47603 q = 2) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d47603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47604 q = 2) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d47604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47605 q = 2) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d47605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro40008 (p : Pattern) (selected : d47611 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d47606 q = 2) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d47606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro40007 q selected
    | true =>
      simp only [d47606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d47607 q = 2) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d47607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d47607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d47608 q = 2) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d47608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d47608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d47609 q = 2) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d47609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d47609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d47610 q = 2) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d47610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d47611 q = 2) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d47611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d47611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro40009 (p : Pattern) (selected : d381091 p = 0) : d381137 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d381087 q = 0) : d381133 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d381087, d381133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39913 q selected
    | true =>
      simp only [d381087, d381133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d381088 q = 0) : d381134 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d381088, d381134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d381088, d381134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d381089 q = 0) : d381135 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d381089, d381135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d381089, d381135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d381090 q = 0) : d381136 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d381090, d381136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d381090, d381136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d381091 q = 0) : d381137 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d381091, d381137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d381091, d381137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro40010 (p : Pattern) (selected : d381096 p = 0) : d381142 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d381092 q = 0) : d381138 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d381092, d381138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro40009 q selected
    | true =>
      simp only [d381092, d381138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d381093 q = 0) : d381139 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d381093, d381139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d381093, d381139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d381094 q = 0) : d381140 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d381094, d381140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d381094, d381140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d381095 q = 0) : d381141 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d381095, d381141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d381095, d381141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d381096 q = 0) : d381142 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d381096, d381142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d381096, d381142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro40011 (p : Pattern) (selected : d381102 p = 0) : d381148 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d381097 q = 0) : d381143 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d381097, d381143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro40010 q selected
    | true =>
      simp only [d381097, d381143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d381098 q = 0) : d381144 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d381098, d381144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d381098, d381144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d381099 q = 0) : d381145 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d381099, d381145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d381099, d381145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d381100 q = 0) : d381146 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d381100, d381146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d381100, d381146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d381101 q = 0) : d381147 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d381101, d381147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d381101, d381147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d381102 q = 0) : d381148 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d381102, d381148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d381102, d381148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro40012 (p : Pattern) (selected : d381108 p = 0) : d381154 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d381103 q = 0) : d381149 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d381103, d381149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro40011 q selected
    | true =>
      simp only [d381103, d381149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d381104 q = 0) : d381150 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d381104, d381150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d381104, d381150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d381105 q = 0) : d381151 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d381105, d381151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d381105, d381151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d381106 q = 0) : d381152 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d381106, d381152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d381106, d381152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d381107 q = 0) : d381153 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d381107, d381153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d381107, d381153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d381108 q = 0) : d381154 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d381108, d381154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d381108, d381154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro40013 (p : Pattern) (selected : d381114 p = 0) : d381160 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d381109 q = 0) : d381155 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d381109, d381155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro40012 q selected
    | true =>
      simp only [d381109, d381155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d381110 q = 0) : d381156 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d381110, d381156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d381110, d381156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d381111 q = 0) : d381157 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d381111, d381157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d381111, d381157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d381112 q = 0) : d381158 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d381112, d381158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d381112, d381158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d381113 q = 0) : d381159 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d381113, d381159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d381113, d381159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d381114 q = 0) : d381160 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d381114, d381160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d381114, d381160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro40014 (p : Pattern) (selected : d381120 p = 0) : d381166 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d381115 q = 0) : d381161 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d381115, d381161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro40013 q selected
    | true =>
      simp only [d381115, d381161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d381116 q = 0) : d381162 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d381116, d381162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d381116, d381162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d381117 q = 0) : d381163 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d381117, d381163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d381117, d381163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d381118 q = 0) : d381164 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d381118, d381164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d381118, d381164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d381119 q = 0) : d381165 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d381119, d381165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d381119, d381165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d381120 q = 0) : d381166 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d381120, d381166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d381120, d381166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro40015 (p : Pattern) (selected : d381126 p = 0) : d381172 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d381121 q = 0) : d381167 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d381121, d381167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro40014 q selected
    | true =>
      simp only [d381121, d381167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d381122 q = 0) : d381168 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d381122, d381168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d381122, d381168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d381123 q = 0) : d381169 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d381123, d381169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d381123, d381169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d381124 q = 0) : d381170 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d381124, d381170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d381124, d381170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d381125 q = 0) : d381171 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d381125, d381171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d381125, d381171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d381126 q = 0) : d381172 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d381126, d381172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d381126, d381172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro40016 (p : Pattern) (selected : d381132 p = 0) : d381178 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d381127 q = 0) : d381173 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d381127, d381173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro40015 q selected
    | true =>
      simp only [d381127, d381173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d381128 q = 0) : d381174 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d381128, d381174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d381128, d381174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d381129 q = 0) : d381175 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d381129, d381175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d381129, d381175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d381130 q = 0) : d381176 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d381130, d381176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d381130, d381176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d381131 q = 0) : d381177 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d381131, d381177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d381131, d381177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d381132 q = 0) : d381178 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d381132, d381178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d381132, d381178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro40017 (p : Pattern) (selected : d381091 p = 1) : d381183 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d381087 q = 1) : d381179 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d381087, d381179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39930 q selected
    | true =>
      simp only [d381087, d381179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d381088 q = 1) : d381180 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d381088, d381180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d381088, d381180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d381089 q = 1) : d381181 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d381089, d381181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d381089, d381181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d381090 q = 1) : d381182 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d381090, d381182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d381090, d381182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d381091 q = 1) : d381183 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d381091, d381183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d381091, d381183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro40018 (p : Pattern) (selected : d381096 p = 1) : d381188 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d381092 q = 1) : d381184 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d381092, d381184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro40017 q selected
    | true =>
      simp only [d381092, d381184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d381093 q = 1) : d381185 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d381093, d381185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d381093, d381185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d381094 q = 1) : d381186 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d381094, d381186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d381094, d381186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d381095 q = 1) : d381187 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d381095, d381187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d381095, d381187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d381096 q = 1) : d381188 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d381096, d381188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d381096, d381188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro40019 (p : Pattern) (selected : d381102 p = 1) : d381194 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d381097 q = 1) : d381189 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d381097, d381189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro40018 q selected
    | true =>
      simp only [d381097, d381189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d381098 q = 1) : d381190 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d381098, d381190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d381098, d381190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d381099 q = 1) : d381191 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d381099, d381191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d381099, d381191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d381100 q = 1) : d381192 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d381100, d381192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d381100, d381192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d381101 q = 1) : d381193 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d381101, d381193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d381101, d381193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d381102 q = 1) : d381194 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d381102, d381194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d381102, d381194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro40020 (p : Pattern) (selected : d381108 p = 1) : d381200 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d381103 q = 1) : d381195 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d381103, d381195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro40019 q selected
    | true =>
      simp only [d381103, d381195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d381104 q = 1) : d381196 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d381104, d381196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d381104, d381196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d381105 q = 1) : d381197 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d381105, d381197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d381105, d381197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d381106 q = 1) : d381198 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d381106, d381198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d381106, d381198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d381107 q = 1) : d381199 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d381107, d381199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d381107, d381199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d381108 q = 1) : d381200 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d381108, d381200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d381108, d381200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro40021 (p : Pattern) (selected : d381114 p = 1) : d381206 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d381109 q = 1) : d381201 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d381109, d381201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro40020 q selected
    | true =>
      simp only [d381109, d381201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d381110 q = 1) : d381202 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d381110, d381202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d381110, d381202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d381111 q = 1) : d381203 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d381111, d381203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d381111, d381203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d381112 q = 1) : d381204 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d381112, d381204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d381112, d381204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d381113 q = 1) : d381205 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d381113, d381205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d381113, d381205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d381114 q = 1) : d381206 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d381114, d381206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d381114, d381206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro40022 (p : Pattern) (selected : d381120 p = 1) : d381212 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d381115 q = 1) : d381207 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d381115, d381207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro40021 q selected
    | true =>
      simp only [d381115, d381207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d381116 q = 1) : d381208 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d381116, d381208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d381116, d381208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d381117 q = 1) : d381209 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d381117, d381209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d381117, d381209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d381118 q = 1) : d381210 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d381118, d381210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d381118, d381210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d381119 q = 1) : d381211 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d381119, d381211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d381119, d381211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d381120 q = 1) : d381212 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d381120, d381212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d381120, d381212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro40023 (p : Pattern) (selected : d381126 p = 1) : d381218 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d381121 q = 1) : d381213 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d381121, d381213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro40022 q selected
    | true =>
      simp only [d381121, d381213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d381122 q = 1) : d381214 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d381122, d381214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d381122, d381214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d381123 q = 1) : d381215 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d381123, d381215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d381123, d381215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d381124 q = 1) : d381216 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d381124, d381216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d381124, d381216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d381125 q = 1) : d381217 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d381125, d381217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d381125, d381217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d381126 q = 1) : d381218 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d381126, d381218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d381126, d381218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro40024 (p : Pattern) (selected : d381132 p = 1) : d381224 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d381127 q = 1) : d381219 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d381127, d381219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro40023 q selected
    | true =>
      simp only [d381127, d381219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d381128 q = 1) : d381220 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d381128, d381220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d381128, d381220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d381129 q = 1) : d381221 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d381129, d381221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d381129, d381221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d381130 q = 1) : d381222 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d381130, d381222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d381130, d381222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d381131 q = 1) : d381223 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d381131, d381223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d381131, d381223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d381132 q = 1) : d381224 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d381132, d381224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d381132, d381224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro40025 (p : Pattern) (selected : d47562 p = 0) : d380856 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d96 q = 0) : d51948 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, d51948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96, d51948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro199 q selected
  have h2 (q : Pattern) (selected : d97 q = 0) : d51949 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, d51949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d97, d51949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d98 q = 0) : d51950 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, d51950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d98, d51950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d99 q = 0) : d51951 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, d51951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99, d51951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d47562 q = 0) : d380856 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d47562, d380856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d47562, d380856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro40026 (p : Pattern) (selected : d381256 p = 0) : d381303 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d381251 q = 0) : d381298 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d381251, d381298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro40025 q selected
    | true =>
      simp only [d381251, d381298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d381252 q = 0) : d381299 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d381252, d381299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d381252, d381299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d381253 q = 0) : d381300 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d381253, d381300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d381253, d381300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d381254 q = 0) : d381301 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d381254, d381301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d381254, d381301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d381255 q = 0) : d381302 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d381255, d381302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d381255, d381302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d381256 q = 0) : d381303 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d381256, d381303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d381256, d381303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro40027 (p : Pattern) (selected : d381261 p = 0) : d381308 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d381257 q = 0) : d381304 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d381257, d381304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro40026 q selected
    | true =>
      simp only [d381257, d381304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d381258 q = 0) : d381305 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d381258, d381305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d381258, d381305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d381259 q = 0) : d381306 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d381259, d381306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d381259, d381306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d381260 q = 0) : d381307 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d381260, d381307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d381260, d381307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d381261 q = 0) : d381308 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d381261, d381308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d381261, d381308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro40028 (p : Pattern) (selected : d381267 p = 0) : d381314 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d381262 q = 0) : d381309 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d381262, d381309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro40027 q selected
    | true =>
      simp only [d381262, d381309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d381263 q = 0) : d381310 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d381263, d381310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d381263, d381310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d381264 q = 0) : d381311 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d381264, d381311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d381264, d381311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d381265 q = 0) : d381312 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d381265, d381312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d381265, d381312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d381266 q = 0) : d381313 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d381266, d381313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d381266, d381313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d381267 q = 0) : d381314 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d381267, d381314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d381267, d381314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro40029 (p : Pattern) (selected : d381273 p = 0) : d381320 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d381268 q = 0) : d381315 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d381268, d381315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro40028 q selected
    | true =>
      simp only [d381268, d381315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d381269 q = 0) : d381316 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d381269, d381316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d381269, d381316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d381270 q = 0) : d381317 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d381270, d381317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d381270, d381317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d381271 q = 0) : d381318 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d381271, d381318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d381271, d381318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d381272 q = 0) : d381319 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d381272, d381319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d381272, d381319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d381273 q = 0) : d381320 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d381273, d381320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d381273, d381320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro40030 (p : Pattern) (selected : d381279 p = 0) : d381326 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d381274 q = 0) : d381321 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d381274, d381321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro40029 q selected
    | true =>
      simp only [d381274, d381321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d381275 q = 0) : d381322 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d381275, d381322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d381275, d381322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d381276 q = 0) : d381323 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d381276, d381323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d381276, d381323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d381277 q = 0) : d381324 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d381277, d381324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d381277, d381324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d381278 q = 0) : d381325 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d381278, d381325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d381278, d381325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d381279 q = 0) : d381326 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d381279, d381326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d381279, d381326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro40031 (p : Pattern) (selected : d381285 p = 0) : d381332 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d381280 q = 0) : d381327 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d381280, d381327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro40030 q selected
    | true =>
      simp only [d381280, d381327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d381281 q = 0) : d381328 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d381281, d381328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d381281, d381328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d381282 q = 0) : d381329 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d381282, d381329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d381282, d381329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d381283 q = 0) : d381330 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d381283, d381330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d381283, d381330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d381284 q = 0) : d381331 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d381284, d381331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d381284, d381331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d381285 q = 0) : d381332 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d381285, d381332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d381285, d381332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro40032 (p : Pattern) (selected : d381291 p = 0) : d381338 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d381286 q = 0) : d381333 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d381286, d381333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro40031 q selected
    | true =>
      simp only [d381286, d381333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d381287 q = 0) : d381334 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d381287, d381334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d381287, d381334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d381288 q = 0) : d381335 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d381288, d381335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d381288, d381335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d381289 q = 0) : d381336 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d381289, d381336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d381289, d381336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d381290 q = 0) : d381337 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d381290, d381337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d381290, d381337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d381291 q = 0) : d381338 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d381291, d381338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d381291, d381338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro40033 (p : Pattern) (selected : d381297 p = 0) : d381344 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d381292 q = 0) : d381339 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d381292, d381339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro40032 q selected
    | true =>
      simp only [d381292, d381339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d381293 q = 0) : d381340 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d381293, d381340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d381293, d381340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d381294 q = 0) : d381341 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d381294, d381341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d381294, d381341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d381295 q = 0) : d381342 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d381295, d381342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d381295, d381342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d381296 q = 0) : d381343 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d381296, d381343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d381296, d381343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d381297 q = 0) : d381344 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d381297, d381344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d381297, d381344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro40034 (p : Pattern) (selected : d381297 p = 1) : d381297 p = 1 := by
  have h0 (q : Pattern) (selected : d381297 q = 1) : d381297 q = 1 := by
    exact selected
  exact h0 p selected
end NetHack.Soko22Hazard87
