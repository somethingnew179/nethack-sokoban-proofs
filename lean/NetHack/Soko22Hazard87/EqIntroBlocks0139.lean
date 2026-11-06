import NetHack.Soko22Hazard87.EqIntroBlocks0138
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro34750 (p : Pattern) (selected : d333484 p = 0) : d335585 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333479 q = 0) : d335580 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333479, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34749 q selected
    | true =>
      simp only [d333479, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333480 q = 0) : d335581 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333480, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333480, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333481 q = 0) : d335582 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333481, d335582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333481, d335582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333482 q = 0) : d335583 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333482, d335583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333482, d335583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333483 q = 0) : d335584 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d333483, d335584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333483, d335584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333484 q = 0) : d335585 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d333484, d335585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333484, d335585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34751 (p : Pattern) (selected : d333490 p = 0) : d335591 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333485 q = 0) : d335586 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d333485, d335586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34750 q selected
    | true =>
      simp only [d333485, d335586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333486 q = 0) : d335587 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d333486, d335587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333486, d335587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333487 q = 0) : d335588 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d333487, d335588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333487, d335588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333488 q = 0) : d335589 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d333488, d335589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333488, d335589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333489 q = 0) : d335590 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d333489, d335590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333489, d335590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333490 q = 0) : d335591 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d333490, d335591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333490, d335591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34752 (p : Pattern) (selected : d333496 p = 0) : d335597 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333491 q = 0) : d335592 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333491, d335592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34751 q selected
    | true =>
      simp only [d333491, d335592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333492 q = 0) : d335593 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333492, d335593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333492, d335593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333493 q = 0) : d335594 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333493, d335594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333493, d335594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333494 q = 0) : d335595 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333494, d335595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333494, d335595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333495 q = 0) : d335596 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333495, d335596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333495, d335596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333496 q = 0) : d335597 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333496, d335597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333496, d335597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro34753 (p : Pattern) (selected : d333502 p = 0) : d335603 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333497 q = 0) : d335598 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333497, d335598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34752 q selected
    | true =>
      simp only [d333497, d335598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333498 q = 0) : d335599 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333498, d335599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333498, d335599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333499 q = 0) : d335600 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333499, d335600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333499, d335600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333500 q = 0) : d335601 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333500, d335601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333500, d335601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333501 q = 0) : d335602 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333501, d335602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333501, d335602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333502 q = 0) : d335603 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333502, d335603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333502, d335603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro34754 (p : Pattern) (selected : d333503 p = 0) : d335604 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333491 q = 0) : d335592 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333491, d335592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34751 q selected
    | true =>
      simp only [d333491, d335592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333492 q = 0) : d335593 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333492, d335593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333492, d335593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333493 q = 0) : d335594 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333493, d335594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333493, d335594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333494 q = 0) : d335595 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333494, d335595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333494, d335595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333495 q = 0) : d335596 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333495, d335596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333495, d335596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333503 q = 0) : d335604 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333503, d335604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333503, d335604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34755 (p : Pattern) (selected : d333509 p = 0) : d335610 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333497 q = 0) : d335598 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333497, d335598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34752 q selected
    | true =>
      simp only [d333497, d335598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333498 q = 0) : d335599 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333498, d335599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333498, d335599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333499 q = 0) : d335600 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333499, d335600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333499, d335600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333500 q = 0) : d335601 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333500, d335601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333500, d335601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333501 q = 0) : d335602 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333501, d335602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333501, d335602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333504 q = 0) : d335605 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333504, d335605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34754 q selected
    | true =>
      simp only [d333504, d335605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333505 q = 0) : d335606 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333505, d335606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333505, d335606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d333506 q = 0) : d335607 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333506, d335607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333506, d335607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d333507 q = 0) : d335608 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333507, d335608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333507, d335608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333508 q = 0) : d335609 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333508, d335609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333508, d335609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d333509 q = 0) : d335610 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333509, d335610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333509, d335610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro34756 (p : Pattern) (selected : d333514 p = 0) : d335615 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333504 q = 0) : d335605 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333504, d335605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34754 q selected
    | true =>
      simp only [d333504, d335605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333505 q = 0) : d335606 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333505, d335606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333505, d335606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333506 q = 0) : d335607 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333506, d335607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333506, d335607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333507 q = 0) : d335608 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333507, d335608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333507, d335608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333508 q = 0) : d335609 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333508, d335609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333508, d335609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333514 q = 0) : d335615 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333514, d335615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333514, d335615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro34757 (p : Pattern) (selected : d333525 p = 0) : d335626 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333520 q = 0) : d335621 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333520, d335621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333520, d335621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34749 q selected
  have h2 (q : Pattern) (selected : d333479 q = 0) : d335580 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333479, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34749 q selected
    | true =>
      simp only [d333479, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333521 q = 0) : d335622 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333521, d335622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333521, d335622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333480 q = 0) : d335581 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333480, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333480, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333522 q = 0) : d335623 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333522, d335623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333522, d335623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333523 q = 0) : d335624 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333523, d335624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333523, d335624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333524 q = 0) : d335625 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d333524, d335625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333524, d335625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d333525 q = 0) : d335626 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d333525, d335626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333525, d335626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro34758 (p : Pattern) (selected : d333531 p = 0) : d335632 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333526 q = 0) : d335627 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d333526, d335627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34757 q selected
    | true =>
      simp only [d333526, d335627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333527 q = 0) : d335628 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d333527, d335628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333527, d335628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333528 q = 0) : d335629 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d333528, d335629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333528, d335629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333529 q = 0) : d335630 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d333529, d335630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333529, d335630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333530 q = 0) : d335631 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d333530, d335631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333530, d335631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333531 q = 0) : d335632 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d333531, d335632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333531, d335632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34759 (p : Pattern) (selected : d333537 p = 0) : d335638 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333532 q = 0) : d335633 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333532, d335633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34758 q selected
    | true =>
      simp only [d333532, d335633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333533 q = 0) : d335634 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333533, d335634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333533, d335634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333534 q = 0) : d335635 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333534, d335635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333534, d335635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333535 q = 0) : d335636 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333535, d335636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333535, d335636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333536 q = 0) : d335637 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333536, d335637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333536, d335637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333537 q = 0) : d335638 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333537, d335638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333537, d335638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34760 (p : Pattern) (selected : d333543 p = 0) : d335644 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333538 q = 0) : d335639 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333538, d335639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34759 q selected
    | true =>
      simp only [d333538, d335639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333539 q = 0) : d335640 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333539, d335640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333539, d335640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333540 q = 0) : d335641 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333540, d335641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333540, d335641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333541 q = 0) : d335642 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333541, d335642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333541, d335642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333542 q = 0) : d335643 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333542, d335643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333542, d335643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333543 q = 0) : d335644 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333543, d335644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333543, d335644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro34761 (p : Pattern) (selected : d333549 p = 0) : d335650 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333510 q = 0) : d335611 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333510, d335611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34753 q selected
    | true =>
      simp only [d333510, d335611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34755 q selected
  have h2 (q : Pattern) (selected : d333511 q = 0) : d335612 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333511, d335612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333511, d335612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333512 q = 0) : d335613 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333512, d335613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333512, d335613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333513 q = 0) : d335614 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333513, d335614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333513, d335614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333515 q = 0) : d335616 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333515, d335616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333515, d335616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34756 q selected
  have h6 (q : Pattern) (selected : d333516 q = 0) : d335617 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333516, d335617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333516, d335617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333517 q = 0) : d335618 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333517, d335618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333517, d335618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d333518 q = 0) : d335619 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333518, d335619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333518, d335619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d333519 q = 0) : d335620 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d333519, d335620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333519, d335620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333544 q = 0) : d335645 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333544, d335645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333544, d335645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34760 q selected
  have h11 (q : Pattern) (selected : d333545 q = 0) : d335646 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333545, d335646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d333545, d335646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d333546 q = 0) : d335647 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333546, d335647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d333546, d335647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d333547 q = 0) : d335648 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333547, d335648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d333547, d335648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d333548 q = 0) : d335649 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d333548, d335649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d333548, d335649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d333549 q = 0) : d335650 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d333549, d335650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d333549, d335650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro34762 (p : Pattern) (selected : d333559 p = 0) : d335660 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333497 q = 0) : d335598 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333497, d335598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34752 q selected
    | true =>
      simp only [d333497, d335598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333555 q = 0) : d335656 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333555, d335656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333555, d335656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333556 q = 0) : d335657 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333556, d335657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333556, d335657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333557 q = 0) : d335658 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333557, d335658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333557, d335658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333558 q = 0) : d335659 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333558, d335659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333558, d335659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333559 q = 0) : d335660 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333559, d335660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333559, d335660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro34763 (p : Pattern) (selected : d333566 p = 0) : d335667 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333497 q = 0) : d335598 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333497, d335598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34752 q selected
    | true =>
      simp only [d333497, d335598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333555 q = 0) : d335656 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333555, d335656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333555, d335656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333556 q = 0) : d335657 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333556, d335657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333556, d335657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333557 q = 0) : d335658 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333557, d335658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333557, d335658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333558 q = 0) : d335659 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333558, d335659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333558, d335659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333504 q = 0) : d335605 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333504, d335605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34754 q selected
    | true =>
      simp only [d333504, d335605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333562 q = 0) : d335663 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333562, d335663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333562, d335663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333563 q = 0) : d335664 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333563, d335664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333563, d335664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d333564 q = 0) : d335665 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333564, d335665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333564, d335665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333565 q = 0) : d335666 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333565, d335666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333565, d335666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d333566 q = 0) : d335667 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333566, d335667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333566, d335667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro34764 (p : Pattern) (selected : d333571 p = 0) : d335672 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333491 q = 0) : d335592 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333491, d335592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34751 q selected
    | true =>
      simp only [d333491, d335592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333492 q = 0) : d335593 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333492, d335593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333492, d335593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333493 q = 0) : d335594 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333493, d335594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333493, d335594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333494 q = 0) : d335595 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333494, d335595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333494, d335595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333570 q = 0) : d335671 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333570, d335671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333570, d335671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333571 q = 0) : d335672 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333571, d335672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333571, d335672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro34765 (p : Pattern) (selected : d333578 p = 0) : d335679 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333491 q = 0) : d335592 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333491, d335592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34751 q selected
    | true =>
      simp only [d333491, d335592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333492 q = 0) : d335593 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333492, d335593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333492, d335593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333493 q = 0) : d335594 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333493, d335594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333493, d335594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333576 q = 0) : d335677 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333576, d335677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333576, d335677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333577 q = 0) : d335678 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333577, d335678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333577, d335678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333578 q = 0) : d335679 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333578, d335679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333578, d335679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro34766 (p : Pattern) (selected : d333585 p = 0) : d335686 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333582 q = 0) : d335683 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333582, d335683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro204 q selected
    | true =>
      simp only [d333582, d335683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333475 q = 0) : d335576 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333475, d335576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
    | true =>
      simp only [d333475, d335576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333583 q = 0) : d335684 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d333583, d335684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333583, d335684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333584 q = 0) : d335685 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d333584, d335685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333584, d335685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333476 q = 0) : d335577 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d333476, d335577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333476, d335577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333477 q = 0) : d335578 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d333477, d335578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333477, d335578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333585 q = 0) : d335686 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d333585, d335686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333585, d335686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro34767 (p : Pattern) (selected : d333591 p = 0) : d335692 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333586 q = 0) : d335687 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333586, d335687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34766 q selected
    | true =>
      simp only [d333586, d335687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333587 q = 0) : d335688 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333587, d335688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333587, d335688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333588 q = 0) : d335689 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333588, d335689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333588, d335689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333589 q = 0) : d335690 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333589, d335690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333589, d335690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333479 q = 0) : d335580 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333479, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34749 q selected
    | true =>
      simp only [d333479, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333480 q = 0) : d335581 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333480, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333480, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333481 q = 0) : d335582 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333481, d335582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333481, d335582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333482 q = 0) : d335583 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333482, d335583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333482, d335583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d333590 q = 0) : d335691 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d333590, d335691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333590, d335691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333591 q = 0) : d335692 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d333591, d335692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d333591, d335692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro34768 (p : Pattern) (selected : d333597 p = 0) : d335698 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333592 q = 0) : d335693 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d333592, d335693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34767 q selected
    | true =>
      simp only [d333592, d335693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34750 q selected
  have h2 (q : Pattern) (selected : d333593 q = 0) : d335694 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d333593, d335694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333593, d335694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333594 q = 0) : d335695 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d333594, d335695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333594, d335695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333485 q = 0) : d335586 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d333485, d335586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34750 q selected
    | true =>
      simp only [d333485, d335586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333486 q = 0) : d335587 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d333486, d335587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333486, d335587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333487 q = 0) : d335588 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d333487, d335588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333487, d335588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d333595 q = 0) : d335696 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d333595, d335696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333595, d335696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333488 q = 0) : d335589 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d333488, d335589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333488, d335589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d333596 q = 0) : d335697 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d333596, d335697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333596, d335697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333597 q = 0) : d335698 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d333597, d335698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d333597, d335698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro34769 (p : Pattern) (selected : d333603 p = 0) : d335704 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333598 q = 0) : d335699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333598, d335699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34768 q selected
    | true =>
      simp only [d333598, d335699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333599 q = 0) : d335700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333599, d335700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333599, d335700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333491 q = 0) : d335592 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333491, d335592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34751 q selected
    | true =>
      simp only [d333491, d335592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333492 q = 0) : d335593 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333492, d335593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333492, d335593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333600 q = 0) : d335701 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333600, d335701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333600, d335701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333601 q = 0) : d335702 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333601, d335702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333601, d335702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333602 q = 0) : d335703 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333602, d335703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333602, d335703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d333603 q = 0) : d335704 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333603, d335704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333603, d335704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro34770 (p : Pattern) (selected : d333608 p = 0) : d335579 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333605 q = 0) : d335576 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333605, d335576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
    | true =>
      simp only [d333605, d335576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333606 q = 0) : d335577 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d333606, d335577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333606, d335577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333607 q = 0) : d335578 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d333607, d335578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333607, d335578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333608 q = 0) : d335579 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d333608, d335579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333608, d335579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro34771 (p : Pattern) (selected : d333614 p = 0) : d335585 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333609 q = 0) : d335580 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333609, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34770 q selected
    | true =>
      simp only [d333609, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333610 q = 0) : d335581 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333610, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333610, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333611 q = 0) : d335582 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333611, d335582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333611, d335582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333612 q = 0) : d335583 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333612, d335583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333612, d335583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333613 q = 0) : d335584 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d333613, d335584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333613, d335584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333614 q = 0) : d335585 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d333614, d335585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333614, d335585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34772 (p : Pattern) (selected : d333620 p = 0) : d335591 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333615 q = 0) : d335586 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d333615, d335586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34771 q selected
    | true =>
      simp only [d333615, d335586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333616 q = 0) : d335587 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d333616, d335587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333616, d335587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333617 q = 0) : d335588 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d333617, d335588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333617, d335588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333618 q = 0) : d335589 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d333618, d335589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333618, d335589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333619 q = 0) : d335590 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d333619, d335590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333619, d335590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333620 q = 0) : d335591 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d333620, d335591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333620, d335591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34773 (p : Pattern) (selected : d333626 p = 0) : d335597 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333621 q = 0) : d335592 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333621, d335592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34772 q selected
    | true =>
      simp only [d333621, d335592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333622 q = 0) : d335593 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333622, d335593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333622, d335593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333623 q = 0) : d335594 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333623, d335594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333623, d335594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333624 q = 0) : d335595 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333624, d335595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333624, d335595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333625 q = 0) : d335596 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333625, d335596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333625, d335596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333626 q = 0) : d335597 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333626, d335597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333626, d335597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro34774 (p : Pattern) (selected : d333632 p = 0) : d335710 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333572 q = 0) : d335673 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333572, d335673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34764 q selected
    | true =>
      simp only [d333572, d335673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333573 q = 0) : d335674 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333573, d335674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333573, d335674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333574 q = 0) : d335675 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333574, d335675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333574, d335675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333575 q = 0) : d335676 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333575, d335676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333575, d335676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333579 q = 0) : d335680 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333579, d335680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34765 q selected
    | true =>
      simp only [d333579, d335680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333580 q = 0) : d335681 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333580, d335681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333580, d335681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d333581 q = 0) : d335682 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333581, d335682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333581, d335682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d333604 q = 0) : d335705 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333604, d335705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34769 q selected
    | true =>
      simp only [d333604, d335705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34752 q selected
  have h9 (q : Pattern) (selected : d333627 q = 0) : d335598 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333627, d335598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34773 q selected
    | true =>
      simp only [d333627, d335598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d333628 q = 0) : d335706 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333628, d335706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d333628, d335706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d333497 q = 0) : d335598 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333497, d335598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34752 q selected
    | true =>
      simp only [d333497, d335598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d333498 q = 0) : d335599 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333498, d335599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d333498, d335599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d333629 q = 0) : d335707 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333629, d335707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d333629, d335707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d333630 q = 0) : d335708 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333630, d335708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333630, d335708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d333631 q = 0) : d335709 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333631, d335709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333631, d335709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d333632 q = 0) : d335710 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333632, d335710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333632, d335710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro34775 (p : Pattern) (selected : d333633 p = 0) : d335711 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333491 q = 0) : d335592 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333491, d335592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34751 q selected
    | true =>
      simp only [d333491, d335592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333492 q = 0) : d335593 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333492, d335593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333492, d335593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333493 q = 0) : d335594 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333493, d335594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333493, d335594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333494 q = 0) : d335595 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333494, d335595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333494, d335595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333570 q = 0) : d335671 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333570, d335671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333570, d335671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333633 q = 0) : d335711 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333633, d335711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333633, d335711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34776 (p : Pattern) (selected : d333638 p = 0) : d335716 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333491 q = 0) : d335592 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333491, d335592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34751 q selected
    | true =>
      simp only [d333491, d335592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333492 q = 0) : d335593 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333492, d335593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333492, d335593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333493 q = 0) : d335594 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333493, d335594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333493, d335594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333576 q = 0) : d335677 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333576, d335677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333576, d335677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333577 q = 0) : d335678 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333577, d335678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333577, d335678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333638 q = 0) : d335716 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333638, d335716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333638, d335716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34777 (p : Pattern) (selected : d333642 p = 0) : d335720 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333598 q = 0) : d335699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333598, d335699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34768 q selected
    | true =>
      simp only [d333598, d335699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333599 q = 0) : d335700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333599, d335700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333599, d335700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333491 q = 0) : d335592 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333491, d335592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34751 q selected
    | true =>
      simp only [d333491, d335592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333492 q = 0) : d335593 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333492, d335593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333492, d335593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333600 q = 0) : d335701 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333600, d335701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333600, d335701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333601 q = 0) : d335702 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333601, d335702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333601, d335702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333602 q = 0) : d335703 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333602, d335703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333602, d335703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d333642 q = 0) : d335720 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333642, d335720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333642, d335720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro34778 (p : Pattern) (selected : d333644 p = 0) : d335604 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333621 q = 0) : d335592 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333621, d335592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34772 q selected
    | true =>
      simp only [d333621, d335592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333622 q = 0) : d335593 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333622, d335593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333622, d335593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333623 q = 0) : d335594 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333623, d335594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333623, d335594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333624 q = 0) : d335595 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333624, d335595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333624, d335595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333625 q = 0) : d335596 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333625, d335596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333625, d335596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333644 q = 0) : d335604 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333644, d335604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333644, d335604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34779 (p : Pattern) (selected : d333650 p = 0) : d335726 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333572 q = 0) : d335673 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333572, d335673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34764 q selected
    | true =>
      simp only [d333572, d335673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333573 q = 0) : d335674 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333573, d335674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333573, d335674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333574 q = 0) : d335675 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333574, d335675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333574, d335675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333575 q = 0) : d335676 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333575, d335676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333575, d335676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333579 q = 0) : d335680 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333579, d335680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34765 q selected
    | true =>
      simp only [d333579, d335680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333580 q = 0) : d335681 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333580, d335681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333580, d335681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d333581 q = 0) : d335682 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333581, d335682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333581, d335682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d333604 q = 0) : d335705 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333604, d335705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34769 q selected
    | true =>
      simp only [d333604, d335705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34752 q selected
  have h9 (q : Pattern) (selected : d333627 q = 0) : d335598 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333627, d335598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34773 q selected
    | true =>
      simp only [d333627, d335598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d333628 q = 0) : d335706 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333628, d335706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d333628, d335706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d333497 q = 0) : d335598 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333497, d335598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34752 q selected
    | true =>
      simp only [d333497, d335598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d333498 q = 0) : d335599 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333498, d335599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d333498, d335599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d333629 q = 0) : d335707 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333629, d335707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d333629, d335707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d333630 q = 0) : d335708 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333630, d335708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333630, d335708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d333631 q = 0) : d335709 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333631, d335709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333631, d335709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d333634 q = 0) : d335712 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333634, d335712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34775 q selected
    | true =>
      simp only [d333634, d335712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d333635 q = 0) : d335713 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333635, d335713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333635, d335713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d333636 q = 0) : d335714 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333636, d335714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d333636, d335714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d333637 q = 0) : d335715 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333637, d335715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333637, d335715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d333639 q = 0) : d335717 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333639, d335717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34776 q selected
    | true =>
      simp only [d333639, d335717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d333640 q = 0) : d335718 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333640, d335718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333640, d335718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d333641 q = 0) : d335719 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333641, d335719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d333641, d335719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d333643 q = 0) : d335721 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333643, d335721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34777 q selected
    | true =>
      simp only [d333643, d335721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34754 q selected
  have h24 (q : Pattern) (selected : d333645 q = 0) : d335605 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333645, d335605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34778 q selected
    | true =>
      simp only [d333645, d335605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d333646 q = 0) : d335722 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333646, d335722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d333646, d335722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d333504 q = 0) : d335605 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333504, d335605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34754 q selected
    | true =>
      simp only [d333504, d335605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d333505 q = 0) : d335606 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333505, d335606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d333505, d335606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d333647 q = 0) : d335723 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333647, d335723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d333647, d335723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d333648 q = 0) : d335724 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333648, d335724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d333648, d335724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d333649 q = 0) : d335725 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333649, d335725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d333649, d335725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d333650 q = 0) : d335726 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333650, d335726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d333650, d335726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro34780 (p : Pattern) (selected : d333652 p = 0) : d335728 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333497 q = 0) : d335598 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333497, d335598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34752 q selected
    | true =>
      simp only [d333497, d335598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333555 q = 0) : d335656 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333555, d335656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333555, d335656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333556 q = 0) : d335657 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333556, d335657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333556, d335657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333557 q = 0) : d335658 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333557, d335658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333557, d335658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333558 q = 0) : d335659 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333558, d335659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333558, d335659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333652 q = 0) : d335728 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333652, d335728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333652, d335728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34781 (p : Pattern) (selected : d333659 p = 0) : d335735 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333643 q = 0) : d335721 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333643, d335721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34777 q selected
    | true =>
      simp only [d333643, d335721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34754 q selected
  have h2 (q : Pattern) (selected : d333645 q = 0) : d335605 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333645, d335605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34778 q selected
    | true =>
      simp only [d333645, d335605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333646 q = 0) : d335722 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333646, d335722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333646, d335722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333504 q = 0) : d335605 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333504, d335605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34754 q selected
    | true =>
      simp only [d333504, d335605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333505 q = 0) : d335606 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333505, d335606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333505, d335606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333647 q = 0) : d335723 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333647, d335723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333647, d335723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d333657 q = 0) : d335733 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333657, d335733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333657, d335733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333658 q = 0) : d335734 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333658, d335734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333658, d335734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d333659 q = 0) : d335735 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333659, d335735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333659, d335735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro34782 (p : Pattern) (selected : d333670 p = 0) : d335746 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333665 q = 0) : d335741 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333665, d335741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333665, d335741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34766 q selected
  have h2 (q : Pattern) (selected : d333586 q = 0) : d335687 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333586, d335687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34766 q selected
    | true =>
      simp only [d333586, d335687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333666 q = 0) : d335742 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333666, d335742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333666, d335742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333587 q = 0) : d335688 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333587, d335688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333587, d335688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333667 q = 0) : d335743 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333667, d335743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333667, d335743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333668 q = 0) : d335744 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333668, d335744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333668, d335744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333520 q = 0) : d335621 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333520, d335621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333520, d335621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34749 q selected
  have h8 (q : Pattern) (selected : d333479 q = 0) : d335580 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333479, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34749 q selected
    | true =>
      simp only [d333479, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d333521 q = 0) : d335622 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333521, d335622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333521, d335622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333480 q = 0) : d335581 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333480, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d333480, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d333522 q = 0) : d335623 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333522, d335623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d333522, d335623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d333523 q = 0) : d335624 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333523, d335624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d333523, d335624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d333669 q = 0) : d335745 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d333669, d335745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333669, d335745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d333670 q = 0) : d335746 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d333670, d335746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d333670, d335746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h14 p selected
theorem eqIntro34783 (p : Pattern) (selected : d333676 p = 0) : d335752 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333671 q = 0) : d335747 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d333671, d335747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34782 q selected
    | true =>
      simp only [d333671, d335747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34757 q selected
  have h2 (q : Pattern) (selected : d333672 q = 0) : d335748 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d333672, d335748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333672, d335748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333673 q = 0) : d335749 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d333673, d335749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333673, d335749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333526 q = 0) : d335627 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d333526, d335627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34757 q selected
    | true =>
      simp only [d333526, d335627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333527 q = 0) : d335628 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d333527, d335628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333527, d335628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333528 q = 0) : d335629 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d333528, d335629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333528, d335629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d333674 q = 0) : d335750 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d333674, d335750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333674, d335750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333529 q = 0) : d335630 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d333529, d335630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333529, d335630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d333675 q = 0) : d335751 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d333675, d335751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333675, d335751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333676 q = 0) : d335752 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d333676, d335752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d333676, d335752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro34784 (p : Pattern) (selected : d333682 p = 0) : d335758 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333677 q = 0) : d335753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333677, d335753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34783 q selected
    | true =>
      simp only [d333677, d335753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333678 q = 0) : d335754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333678, d335754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333678, d335754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333532 q = 0) : d335633 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333532, d335633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34758 q selected
    | true =>
      simp only [d333532, d335633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333533 q = 0) : d335634 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333533, d335634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333533, d335634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333679 q = 0) : d335755 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333679, d335755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333679, d335755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333680 q = 0) : d335756 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333680, d335756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333680, d335756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333681 q = 0) : d335757 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333681, d335757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333681, d335757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d333682 q = 0) : d335758 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333682, d335758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333682, d335758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro34785 (p : Pattern) (selected : d333689 p = 0) : d335626 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333684 q = 0) : d335621 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333684, d335621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333684, d335621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34770 q selected
  have h2 (q : Pattern) (selected : d333609 q = 0) : d335580 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333609, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34770 q selected
    | true =>
      simp only [d333609, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333685 q = 0) : d335622 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333685, d335622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333685, d335622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333610 q = 0) : d335581 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333610, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333610, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333686 q = 0) : d335623 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333686, d335623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333686, d335623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333687 q = 0) : d335624 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333687, d335624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333687, d335624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333688 q = 0) : d335625 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d333688, d335625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333688, d335625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d333689 q = 0) : d335626 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d333689, d335626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333689, d335626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro34786 (p : Pattern) (selected : d333695 p = 0) : d335632 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333690 q = 0) : d335627 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d333690, d335627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34785 q selected
    | true =>
      simp only [d333690, d335627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333691 q = 0) : d335628 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d333691, d335628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333691, d335628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333692 q = 0) : d335629 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d333692, d335629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333692, d335629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333693 q = 0) : d335630 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d333693, d335630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333693, d335630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333694 q = 0) : d335631 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d333694, d335631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333694, d335631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333695 q = 0) : d335632 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d333695, d335632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333695, d335632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34787 (p : Pattern) (selected : d333701 p = 0) : d335638 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333696 q = 0) : d335633 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333696, d335633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34786 q selected
    | true =>
      simp only [d333696, d335633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333697 q = 0) : d335634 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333697, d335634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333697, d335634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333698 q = 0) : d335635 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333698, d335635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333698, d335635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333699 q = 0) : d335636 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333699, d335636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333699, d335636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333700 q = 0) : d335637 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333700, d335637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333700, d335637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333701 q = 0) : d335638 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333701, d335638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333701, d335638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34788 (p : Pattern) (selected : d333707 p = 0) : d335764 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333683 q = 0) : d335759 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333683, d335759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34784 q selected
    | true =>
      simp only [d333683, d335759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34759 q selected
  have h2 (q : Pattern) (selected : d333702 q = 0) : d335639 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333702, d335639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34787 q selected
    | true =>
      simp only [d333702, d335639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333703 q = 0) : d335760 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333703, d335760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333703, d335760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333538 q = 0) : d335639 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333538, d335639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34759 q selected
    | true =>
      simp only [d333538, d335639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333539 q = 0) : d335640 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333539, d335640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333539, d335640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333704 q = 0) : d335761 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333704, d335761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333704, d335761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d333705 q = 0) : d335762 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333705, d335762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333705, d335762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333706 q = 0) : d335763 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333706, d335763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333706, d335763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d333707 q = 0) : d335764 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333707, d335764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333707, d335764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro34789 (p : Pattern) (selected : d333713 p = 0) : d335770 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333560 q = 0) : d335661 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333560, d335661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333560, d335661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34762 q selected
  have h2 (q : Pattern) (selected : d333561 q = 0) : d335662 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333561, d335662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333561, d335662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333567 q = 0) : d335668 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333567, d335668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34762 q selected
    | true =>
      simp only [d333567, d335668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34763 q selected
  have h4 (q : Pattern) (selected : d333568 q = 0) : d335669 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333568, d335669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333568, d335669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333569 q = 0) : d335670 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333569, d335670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333569, d335670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333651 q = 0) : d335727 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333651, d335727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34774 q selected
    | true =>
      simp only [d333651, d335727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34779 q selected
  have h7 (q : Pattern) (selected : d333653 q = 0) : d335729 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333653, d335729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34780 q selected
    | true =>
      simp only [d333653, d335729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d333654 q = 0) : d335730 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333654, d335730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333654, d335730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d333655 q = 0) : d335731 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333655, d335731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d333655, d335731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d333656 q = 0) : d335732 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333656, d335732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333656, d335732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d333660 q = 0) : d335736 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333660, d335736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333660, d335736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34781 q selected
  have h12 (q : Pattern) (selected : d333661 q = 0) : d335737 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333661, d335737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d333661, d335737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d333662 q = 0) : d335738 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333662, d335738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d333662, d335738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d333663 q = 0) : d335739 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333663, d335739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d333663, d335739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d333664 q = 0) : d335740 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d333664, d335740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d333664, d335740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d333708 q = 0) : d335765 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333708, d335765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333708, d335765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34788 q selected
  have h17 (q : Pattern) (selected : d333709 q = 0) : d335766 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333709, d335766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d333709, d335766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d333710 q = 0) : d335767 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333710, d335767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d333710, d335767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d333711 q = 0) : d335768 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333711, d335768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d333711, d335768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d333712 q = 0) : d335769 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d333712, d335769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d333712, d335769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d333713 q = 0) : d335770 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d333713, d335770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d333713, d335770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro34790 (p : Pattern) (selected : d333719 p = 0) : d335776 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333550 q = 0) : d335651 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d333550, d335651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333550, d335651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34761 q selected
  have h2 (q : Pattern) (selected : d333551 q = 0) : d335652 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d333551, d335652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333551, d335652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333552 q = 0) : d335653 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d333552, d335653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333552, d335653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333553 q = 0) : d335654 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d333553, d335654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333553, d335654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333554 q = 0) : d335655 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d333554, d335655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333554, d335655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333714 q = 0) : d335771 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d333714, d335771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333714, d335771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34789 q selected
  have h7 (q : Pattern) (selected : d333715 q = 0) : d335772 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d333715, d335772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333715, d335772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333716 q = 0) : d335773 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d333716, d335773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333716, d335773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d333717 q = 0) : d335774 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d333717, d335774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333717, d335774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333718 q = 0) : d335775 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d333718, d335775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333718, d335775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d333719 q = 0) : d335776 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d333719, d335776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333719, d335776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro34791 (p : Pattern) (selected : d333724 p = 0) : d335781 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333604 q = 0) : d335705 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333604, d335705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34769 q selected
    | true =>
      simp only [d333604, d335705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34752 q selected
  have h2 (q : Pattern) (selected : d333720 q = 0) : d335777 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333720, d335777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333720, d335777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333721 q = 0) : d335778 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333721, d335778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333721, d335778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333722 q = 0) : d335779 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333722, d335779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333722, d335779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333723 q = 0) : d335780 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333723, d335780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333723, d335780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333724 q = 0) : d335781 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333724, d335781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333724, d335781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro34792 (p : Pattern) (selected : d333731 p = 0) : d335788 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333604 q = 0) : d335705 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333604, d335705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34769 q selected
    | true =>
      simp only [d333604, d335705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34752 q selected
  have h2 (q : Pattern) (selected : d333720 q = 0) : d335777 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333720, d335777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333720, d335777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333721 q = 0) : d335778 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333721, d335778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333721, d335778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333722 q = 0) : d335779 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333722, d335779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333722, d335779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333723 q = 0) : d335780 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333723, d335780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333723, d335780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333643 q = 0) : d335721 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333643, d335721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34777 q selected
    | true =>
      simp only [d333643, d335721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34754 q selected
  have h7 (q : Pattern) (selected : d333727 q = 0) : d335784 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333727, d335784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333727, d335784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333728 q = 0) : d335785 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333728, d335785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333728, d335785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d333729 q = 0) : d335786 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333729, d335786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333729, d335786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333730 q = 0) : d335787 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333730, d335787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333730, d335787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d333731 q = 0) : d335788 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333731, d335788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333731, d335788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro34793 (p : Pattern) (selected : d333736 p = 0) : d335793 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333598 q = 0) : d335699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333598, d335699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34768 q selected
    | true =>
      simp only [d333598, d335699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333599 q = 0) : d335700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333599, d335700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333599, d335700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333491 q = 0) : d335592 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333491, d335592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34751 q selected
    | true =>
      simp only [d333491, d335592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333492 q = 0) : d335593 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333492, d335593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333492, d335593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333600 q = 0) : d335701 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333600, d335701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333600, d335701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333601 q = 0) : d335702 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333601, d335702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333601, d335702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333735 q = 0) : d335792 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333735, d335792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333735, d335792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333736 q = 0) : d335793 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333736, d335793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333736, d335793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro34794 (p : Pattern) (selected : d333743 p = 0) : d335800 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333598 q = 0) : d335699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333598, d335699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34768 q selected
    | true =>
      simp only [d333598, d335699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333599 q = 0) : d335700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333599, d335700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333599, d335700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333491 q = 0) : d335592 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333491, d335592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34751 q selected
    | true =>
      simp only [d333491, d335592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333492 q = 0) : d335593 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333492, d335593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333492, d335593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333600 q = 0) : d335701 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333600, d335701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333600, d335701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333741 q = 0) : d335798 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333741, d335798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333741, d335798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d333742 q = 0) : d335799 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333742, d335799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333742, d335799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d333743 q = 0) : d335800 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333743, d335800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333743, d335800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro34795 (p : Pattern) (selected : d333750 p = 0) : d335807 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333747 q = 0) : d335804 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333747, d335804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23495 q selected
    | true =>
      simp only [d333747, d335804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333582 q = 0) : d335683 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333582, d335683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro204 q selected
    | true =>
      simp only [d333582, d335683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333748 q = 0) : d335805 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d333748, d335805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333748, d335805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333749 q = 0) : d335806 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d333749, d335806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333749, d335806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333475 q = 0) : d335576 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333475, d335576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
    | true =>
      simp only [d333475, d335576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333583 q = 0) : d335684 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d333583, d335684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333583, d335684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d333584 q = 0) : d335685 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d333584, d335685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333584, d335685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d333750 q = 0) : d335807 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d333750, d335807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333750, d335807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro34796 (p : Pattern) (selected : d333755 p = 0) : d335812 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333582 q = 0) : d335683 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333582, d335683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro204 q selected
    | true =>
      simp only [d333582, d335683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333475 q = 0) : d335576 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333475, d335576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
    | true =>
      simp only [d333475, d335576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333583 q = 0) : d335684 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d333583, d335684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333583, d335684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333584 q = 0) : d335685 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d333584, d335685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333584, d335685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333755 q = 0) : d335812 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d333755, d335812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333755, d335812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro34797 (p : Pattern) (selected : d333761 p = 0) : d335818 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333751 q = 0) : d335808 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333751, d335808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34795 q selected
    | true =>
      simp only [d333751, d335808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333752 q = 0) : d335809 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333752, d335809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333752, d335809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333753 q = 0) : d335810 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333753, d335810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333753, d335810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333754 q = 0) : d335811 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333754, d335811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333754, d335811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333756 q = 0) : d335813 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333756, d335813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34796 q selected
    | true =>
      simp only [d333756, d335813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333757 q = 0) : d335814 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333757, d335814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333757, d335814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333758 q = 0) : d335815 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333758, d335815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333758, d335815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333759 q = 0) : d335816 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333759, d335816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333759, d335816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d333760 q = 0) : d335817 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d333760, d335817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333760, d335817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333761 q = 0) : d335818 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d333761, d335818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d333761, d335818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro34798 (p : Pattern) (selected : d333770 p = 0) : d335827 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333762 q = 0) : d335819 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d333762, d335819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34797 q selected
    | true =>
      simp only [d333762, d335819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34767 q selected
  have h2 (q : Pattern) (selected : d333763 q = 0) : d335820 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d333763, d335820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333763, d335820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333764 q = 0) : d335821 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d333764, d335821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333764, d335821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333765 q = 0) : d335822 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d333765, d335822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34767 q selected
    | true =>
      simp only [d333765, d335822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333766 q = 0) : d335823 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d333766, d335823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333766, d335823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333767 q = 0) : d335824 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d333767, d335824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333767, d335824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d333768 q = 0) : d335825 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d333768, d335825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333768, d335825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333592 q = 0) : d335693 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d333592, d335693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34767 q selected
    | true =>
      simp only [d333592, d335693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34750 q selected
  have h9 (q : Pattern) (selected : d333593 q = 0) : d335694 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d333593, d335694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333593, d335694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333594 q = 0) : d335695 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d333594, d335695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333594, d335695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d333485 q = 0) : d335586 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d333485, d335586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34750 q selected
    | true =>
      simp only [d333485, d335586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d333486 q = 0) : d335587 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d333486, d335587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333486, d335587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d333487 q = 0) : d335588 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d333487, d335588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333487, d335588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d333595 q = 0) : d335696 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d333595, d335696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d333595, d335696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d333769 q = 0) : d335826 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d333769, d335826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333769, d335826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d333770 q = 0) : d335827 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d333770, d335827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d333770, d335827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro34799 (p : Pattern) (selected : d333776 p = 0) : d335833 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333771 q = 0) : d335828 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333771, d335828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34798 q selected
    | true =>
      simp only [d333771, d335828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333772 q = 0) : d335829 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333772, d335829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333772, d335829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333598 q = 0) : d335699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333598, d335699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34768 q selected
    | true =>
      simp only [d333598, d335699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333599 q = 0) : d335700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333599, d335700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333599, d335700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333773 q = 0) : d335830 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333773, d335830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333773, d335830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333774 q = 0) : d335831 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333774, d335831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333774, d335831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333775 q = 0) : d335832 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333775, d335832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333775, d335832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d333776 q = 0) : d335833 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333776, d335833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333776, d335833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro34800 (p : Pattern) (selected : d333781 p = 0) : d335686 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333778 q = 0) : d335683 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333778, d335683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro239 q selected
    | true =>
      simp only [d333778, d335683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333605 q = 0) : d335576 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333605, d335576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
    | true =>
      simp only [d333605, d335576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333779 q = 0) : d335684 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d333779, d335684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333779, d335684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333780 q = 0) : d335685 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d333780, d335685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333780, d335685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333606 q = 0) : d335577 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d333606, d335577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333606, d335577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333607 q = 0) : d335578 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d333607, d335578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333607, d335578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333781 q = 0) : d335686 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d333781, d335686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333781, d335686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro34801 (p : Pattern) (selected : d333787 p = 0) : d335692 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333782 q = 0) : d335687 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333782, d335687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34800 q selected
    | true =>
      simp only [d333782, d335687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333783 q = 0) : d335688 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333783, d335688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333783, d335688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333784 q = 0) : d335689 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333784, d335689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333784, d335689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333785 q = 0) : d335690 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333785, d335690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333785, d335690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333609 q = 0) : d335580 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333609, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34770 q selected
    | true =>
      simp only [d333609, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333610 q = 0) : d335581 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333610, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333610, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333611 q = 0) : d335582 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333611, d335582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333611, d335582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333612 q = 0) : d335583 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333612, d335583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333612, d335583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d333786 q = 0) : d335691 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d333786, d335691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333786, d335691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333787 q = 0) : d335692 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d333787, d335692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d333787, d335692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro34802 (p : Pattern) (selected : d333793 p = 0) : d335698 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333788 q = 0) : d335693 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d333788, d335693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34801 q selected
    | true =>
      simp only [d333788, d335693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34771 q selected
  have h2 (q : Pattern) (selected : d333789 q = 0) : d335694 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d333789, d335694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333789, d335694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333790 q = 0) : d335695 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d333790, d335695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333790, d335695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333615 q = 0) : d335586 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d333615, d335586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34771 q selected
    | true =>
      simp only [d333615, d335586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333616 q = 0) : d335587 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d333616, d335587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333616, d335587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333617 q = 0) : d335588 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d333617, d335588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333617, d335588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d333791 q = 0) : d335696 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d333791, d335696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333791, d335696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333618 q = 0) : d335589 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d333618, d335589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333618, d335589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d333792 q = 0) : d335697 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d333792, d335697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333792, d335697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333793 q = 0) : d335698 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d333793, d335698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d333793, d335698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro34803 (p : Pattern) (selected : d333799 p = 0) : d335704 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333794 q = 0) : d335699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333794, d335699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34802 q selected
    | true =>
      simp only [d333794, d335699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333795 q = 0) : d335700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333795, d335700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333795, d335700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333621 q = 0) : d335592 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333621, d335592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34772 q selected
    | true =>
      simp only [d333621, d335592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333622 q = 0) : d335593 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333622, d335593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333622, d335593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333796 q = 0) : d335701 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333796, d335701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333796, d335701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333797 q = 0) : d335702 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333797, d335702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333797, d335702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333798 q = 0) : d335703 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333798, d335703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333798, d335703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d333799 q = 0) : d335704 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333799, d335704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333799, d335704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro34804 (p : Pattern) (selected : d333805 p = 0) : d335839 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333598 q = 0) : d335699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333598, d335699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34768 q selected
    | true =>
      simp only [d333598, d335699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333599 q = 0) : d335700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333599, d335700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333599, d335700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333802 q = 0) : d335836 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333802, d335836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333802, d335836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333803 q = 0) : d335837 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333803, d335837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333803, d335837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333804 q = 0) : d335838 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333804, d335838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333804, d335838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333805 q = 0) : d335839 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333805, d335839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333805, d335839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro34805 (p : Pattern) (selected : d333811 p = 0) : d335845 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333737 q = 0) : d335794 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333737, d335794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34793 q selected
    | true =>
      simp only [d333737, d335794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34764 q selected
  have h2 (q : Pattern) (selected : d333738 q = 0) : d335795 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333738, d335795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333738, d335795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333739 q = 0) : d335796 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333739, d335796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333739, d335796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333740 q = 0) : d335797 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333740, d335797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333740, d335797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333744 q = 0) : d335801 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333744, d335801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34794 q selected
    | true =>
      simp only [d333744, d335801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34765 q selected
  have h6 (q : Pattern) (selected : d333745 q = 0) : d335802 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333745, d335802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333745, d335802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d333746 q = 0) : d335803 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333746, d335803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333746, d335803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d333777 q = 0) : d335834 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333777, d335834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34799 q selected
    | true =>
      simp only [d333777, d335834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34769 q selected
  have h9 (q : Pattern) (selected : d333800 q = 0) : d335705 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333800, d335705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34803 q selected
    | true =>
      simp only [d333800, d335705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34773 q selected
  have h10 (q : Pattern) (selected : d333801 q = 0) : d335835 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333801, d335835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d333801, d335835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d333806 q = 0) : d335840 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333806, d335840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34804 q selected
    | true =>
      simp only [d333806, d335840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d333807 q = 0) : d335841 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333807, d335841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d333807, d335841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d333808 q = 0) : d335842 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333808, d335842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d333808, d335842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d333809 q = 0) : d335843 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333809, d335843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333809, d335843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d333810 q = 0) : d335844 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333810, d335844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333810, d335844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d333811 q = 0) : d335845 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333811, d335845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333811, d335845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro34806 (p : Pattern) (selected : d333812 p = 0) : d335846 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333598 q = 0) : d335699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333598, d335699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34768 q selected
    | true =>
      simp only [d333598, d335699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333599 q = 0) : d335700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333599, d335700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333599, d335700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333491 q = 0) : d335592 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333491, d335592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34751 q selected
    | true =>
      simp only [d333491, d335592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333492 q = 0) : d335593 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333492, d335593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333492, d335593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333600 q = 0) : d335701 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333600, d335701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333600, d335701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333601 q = 0) : d335702 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333601, d335702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333601, d335702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333735 q = 0) : d335792 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333735, d335792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333735, d335792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333812 q = 0) : d335846 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333812, d335846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333812, d335846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro34807 (p : Pattern) (selected : d333817 p = 0) : d335851 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333598 q = 0) : d335699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333598, d335699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34768 q selected
    | true =>
      simp only [d333598, d335699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333599 q = 0) : d335700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333599, d335700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333599, d335700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333491 q = 0) : d335592 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333491, d335592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34751 q selected
    | true =>
      simp only [d333491, d335592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333492 q = 0) : d335593 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333492, d335593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333492, d335593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333600 q = 0) : d335701 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333600, d335701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333600, d335701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333741 q = 0) : d335798 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333741, d335798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333741, d335798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d333742 q = 0) : d335799 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333742, d335799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333742, d335799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d333817 q = 0) : d335851 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333817, d335851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333817, d335851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro34808 (p : Pattern) (selected : d333821 p = 0) : d335855 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333771 q = 0) : d335828 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333771, d335828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34798 q selected
    | true =>
      simp only [d333771, d335828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333772 q = 0) : d335829 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333772, d335829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333772, d335829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333598 q = 0) : d335699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333598, d335699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34768 q selected
    | true =>
      simp only [d333598, d335699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333599 q = 0) : d335700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333599, d335700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333599, d335700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333773 q = 0) : d335830 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333773, d335830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333773, d335830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333774 q = 0) : d335831 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333774, d335831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333774, d335831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333775 q = 0) : d335832 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333775, d335832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333775, d335832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d333821 q = 0) : d335855 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333821, d335855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333821, d335855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro34809 (p : Pattern) (selected : d333823 p = 0) : d335720 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333794 q = 0) : d335699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333794, d335699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34802 q selected
    | true =>
      simp only [d333794, d335699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333795 q = 0) : d335700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333795, d335700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333795, d335700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333621 q = 0) : d335592 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333621, d335592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34772 q selected
    | true =>
      simp only [d333621, d335592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333622 q = 0) : d335593 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333622, d335593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333622, d335593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333796 q = 0) : d335701 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333796, d335701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333796, d335701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333797 q = 0) : d335702 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333797, d335702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333797, d335702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333798 q = 0) : d335703 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333798, d335703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333798, d335703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d333823 q = 0) : d335720 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333823, d335720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333823, d335720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro34810 (p : Pattern) (selected : d333826 p = 0) : d335858 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333598 q = 0) : d335699 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333598, d335699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34768 q selected
    | true =>
      simp only [d333598, d335699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333599 q = 0) : d335700 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333599, d335700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333599, d335700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333802 q = 0) : d335836 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333802, d335836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333802, d335836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333803 q = 0) : d335837 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333803, d335837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333803, d335837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333804 q = 0) : d335838 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333804, d335838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333804, d335838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333826 q = 0) : d335858 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333826, d335858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333826, d335858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34811 (p : Pattern) (selected : d333832 p = 0) : d335864 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333737 q = 0) : d335794 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333737, d335794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34793 q selected
    | true =>
      simp only [d333737, d335794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34764 q selected
  have h2 (q : Pattern) (selected : d333738 q = 0) : d335795 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333738, d335795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333738, d335795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333739 q = 0) : d335796 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333739, d335796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333739, d335796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333740 q = 0) : d335797 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333740, d335797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333740, d335797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333744 q = 0) : d335801 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333744, d335801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34794 q selected
    | true =>
      simp only [d333744, d335801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34765 q selected
  have h6 (q : Pattern) (selected : d333745 q = 0) : d335802 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333745, d335802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333745, d335802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d333746 q = 0) : d335803 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333746, d335803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333746, d335803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d333777 q = 0) : d335834 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333777, d335834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34799 q selected
    | true =>
      simp only [d333777, d335834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34769 q selected
  have h9 (q : Pattern) (selected : d333800 q = 0) : d335705 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333800, d335705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34803 q selected
    | true =>
      simp only [d333800, d335705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34773 q selected
  have h10 (q : Pattern) (selected : d333801 q = 0) : d335835 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333801, d335835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d333801, d335835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d333806 q = 0) : d335840 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333806, d335840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34804 q selected
    | true =>
      simp only [d333806, d335840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d333807 q = 0) : d335841 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333807, d335841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d333807, d335841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d333808 q = 0) : d335842 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333808, d335842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d333808, d335842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d333809 q = 0) : d335843 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333809, d335843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333809, d335843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d333810 q = 0) : d335844 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333810, d335844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333810, d335844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d333813 q = 0) : d335847 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333813, d335847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34806 q selected
    | true =>
      simp only [d333813, d335847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34775 q selected
  have h17 (q : Pattern) (selected : d333814 q = 0) : d335848 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333814, d335848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333814, d335848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d333815 q = 0) : d335849 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333815, d335849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d333815, d335849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d333816 q = 0) : d335850 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333816, d335850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333816, d335850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d333818 q = 0) : d335852 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333818, d335852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34807 q selected
    | true =>
      simp only [d333818, d335852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34776 q selected
  have h21 (q : Pattern) (selected : d333819 q = 0) : d335853 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333819, d335853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333819, d335853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d333820 q = 0) : d335854 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333820, d335854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d333820, d335854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d333822 q = 0) : d335856 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333822, d335856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34808 q selected
    | true =>
      simp only [d333822, d335856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34777 q selected
  have h24 (q : Pattern) (selected : d333824 q = 0) : d335721 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333824, d335721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34809 q selected
    | true =>
      simp only [d333824, d335721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34778 q selected
  have h25 (q : Pattern) (selected : d333825 q = 0) : d335857 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333825, d335857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d333825, d335857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d333827 q = 0) : d335859 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333827, d335859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34810 q selected
    | true =>
      simp only [d333827, d335859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d333828 q = 0) : d335860 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333828, d335860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d333828, d335860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d333829 q = 0) : d335861 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333829, d335861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d333829, d335861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d333830 q = 0) : d335862 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333830, d335862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d333830, d335862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d333831 q = 0) : d335863 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333831, d335863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d333831, d335863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d333832 q = 0) : d335864 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333832, d335864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d333832, d335864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro34812 (p : Pattern) (selected : d333834 p = 0) : d335866 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333604 q = 0) : d335705 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333604, d335705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34769 q selected
    | true =>
      simp only [d333604, d335705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34752 q selected
  have h2 (q : Pattern) (selected : d333720 q = 0) : d335777 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333720, d335777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333720, d335777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333721 q = 0) : d335778 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333721, d335778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333721, d335778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333722 q = 0) : d335779 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333722, d335779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333722, d335779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333723 q = 0) : d335780 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333723, d335780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333723, d335780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333497 q = 0) : d335598 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333497, d335598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34752 q selected
    | true =>
      simp only [d333497, d335598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333555 q = 0) : d335656 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333555, d335656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333555, d335656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333556 q = 0) : d335657 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333556, d335657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333556, d335657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d333557 q = 0) : d335658 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333557, d335658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333557, d335658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333558 q = 0) : d335659 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333558, d335659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333558, d335659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d333834 q = 0) : d335866 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333834, d335866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333834, d335866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro34813 (p : Pattern) (selected : d333841 p = 0) : d335873 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333822 q = 0) : d335856 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333822, d335856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34808 q selected
    | true =>
      simp only [d333822, d335856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34777 q selected
  have h2 (q : Pattern) (selected : d333824 q = 0) : d335721 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333824, d335721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34809 q selected
    | true =>
      simp only [d333824, d335721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34778 q selected
  have h3 (q : Pattern) (selected : d333825 q = 0) : d335857 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333825, d335857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333825, d335857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333827 q = 0) : d335859 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333827, d335859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34810 q selected
    | true =>
      simp only [d333827, d335859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333828 q = 0) : d335860 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333828, d335860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333828, d335860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333829 q = 0) : d335861 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333829, d335861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333829, d335861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d333839 q = 0) : d335871 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333839, d335871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333839, d335871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333840 q = 0) : d335872 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333840, d335872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333840, d335872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d333841 q = 0) : d335873 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333841, d335873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333841, d335873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro34814 (p : Pattern) (selected : d333843 p = 0) : d335875 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333504 q = 0) : d335605 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333504, d335605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34754 q selected
    | true =>
      simp only [d333504, d335605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333562 q = 0) : d335663 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333562, d335663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333562, d335663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333563 q = 0) : d335664 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333563, d335664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333563, d335664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333564 q = 0) : d335665 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333564, d335665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333564, d335665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333565 q = 0) : d335666 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333565, d335666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333565, d335666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333843 q = 0) : d335875 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333843, d335875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333843, d335875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro34815 (p : Pattern) (selected : d333858 p = 0) : d335890 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333849 q = 0) : d335881 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333849, d335881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333849, d335881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34795 q selected
  have h2 (q : Pattern) (selected : d333751 q = 0) : d335808 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333751, d335808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34795 q selected
    | true =>
      simp only [d333751, d335808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333850 q = 0) : d335882 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333850, d335882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333850, d335882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333752 q = 0) : d335809 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333752, d335809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333752, d335809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333851 q = 0) : d335883 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333851, d335883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333851, d335883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333852 q = 0) : d335884 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333852, d335884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333852, d335884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333853 q = 0) : d335885 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333853, d335885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333853, d335885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34796 q selected
  have h8 (q : Pattern) (selected : d333756 q = 0) : d335813 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333756, d335813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34796 q selected
    | true =>
      simp only [d333756, d335813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d333854 q = 0) : d335886 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333854, d335886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333854, d335886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333757 q = 0) : d335814 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333757, d335814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d333757, d335814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d333855 q = 0) : d335887 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333855, d335887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d333855, d335887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d333856 q = 0) : d335888 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333856, d335888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d333856, d335888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d333857 q = 0) : d335889 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d333857, d335889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333857, d335889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d333858 q = 0) : d335890 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d333858, d335890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d333858, d335890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h14 p selected
theorem eqIntro34816 (p : Pattern) (selected : d333867 p = 0) : d335899 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333859 q = 0) : d335891 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d333859, d335891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34815 q selected
    | true =>
      simp only [d333859, d335891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34782 q selected
  have h2 (q : Pattern) (selected : d333860 q = 0) : d335892 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d333860, d335892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333860, d335892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333861 q = 0) : d335893 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d333861, d335893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333861, d335893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333862 q = 0) : d335894 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d333862, d335894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34782 q selected
    | true =>
      simp only [d333862, d335894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333863 q = 0) : d335895 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d333863, d335895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333863, d335895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333864 q = 0) : d335896 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d333864, d335896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333864, d335896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d333865 q = 0) : d335897 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d333865, d335897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333865, d335897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333671 q = 0) : d335747 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d333671, d335747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34782 q selected
    | true =>
      simp only [d333671, d335747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34757 q selected
  have h9 (q : Pattern) (selected : d333672 q = 0) : d335748 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d333672, d335748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333672, d335748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333673 q = 0) : d335749 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d333673, d335749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333673, d335749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d333526 q = 0) : d335627 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d333526, d335627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34757 q selected
    | true =>
      simp only [d333526, d335627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d333527 q = 0) : d335628 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d333527, d335628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333527, d335628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d333528 q = 0) : d335629 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d333528, d335629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333528, d335629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d333674 q = 0) : d335750 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d333674, d335750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d333674, d335750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d333866 q = 0) : d335898 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d333866, d335898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333866, d335898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d333867 q = 0) : d335899 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d333867, d335899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d333867, d335899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro34817 (p : Pattern) (selected : d333873 p = 0) : d335905 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333868 q = 0) : d335900 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333868, d335900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34816 q selected
    | true =>
      simp only [d333868, d335900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333869 q = 0) : d335901 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333869, d335901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333869, d335901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333677 q = 0) : d335753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333677, d335753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34783 q selected
    | true =>
      simp only [d333677, d335753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333678 q = 0) : d335754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333678, d335754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333678, d335754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333870 q = 0) : d335902 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333870, d335902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333870, d335902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333871 q = 0) : d335903 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333871, d335903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333871, d335903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333872 q = 0) : d335904 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333872, d335904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333872, d335904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d333873 q = 0) : d335905 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333873, d335905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333873, d335905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro34818 (p : Pattern) (selected : d333880 p = 0) : d335746 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333875 q = 0) : d335741 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333875, d335741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333875, d335741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34800 q selected
  have h2 (q : Pattern) (selected : d333782 q = 0) : d335687 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333782, d335687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34800 q selected
    | true =>
      simp only [d333782, d335687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333876 q = 0) : d335742 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333876, d335742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333876, d335742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333783 q = 0) : d335688 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333783, d335688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333783, d335688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333877 q = 0) : d335743 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333877, d335743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333877, d335743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333878 q = 0) : d335744 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333878, d335744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333878, d335744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333684 q = 0) : d335621 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333684, d335621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333684, d335621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34770 q selected
  have h8 (q : Pattern) (selected : d333609 q = 0) : d335580 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333609, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34770 q selected
    | true =>
      simp only [d333609, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d333685 q = 0) : d335622 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333685, d335622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333685, d335622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333610 q = 0) : d335581 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333610, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d333610, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d333686 q = 0) : d335623 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333686, d335623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d333686, d335623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d333687 q = 0) : d335624 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333687, d335624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d333687, d335624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d333879 q = 0) : d335745 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d333879, d335745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333879, d335745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d333880 q = 0) : d335746 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d333880, d335746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d333880, d335746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h14 p selected
theorem eqIntro34819 (p : Pattern) (selected : d333886 p = 0) : d335752 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333881 q = 0) : d335747 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d333881, d335747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34818 q selected
    | true =>
      simp only [d333881, d335747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34785 q selected
  have h2 (q : Pattern) (selected : d333882 q = 0) : d335748 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d333882, d335748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333882, d335748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333883 q = 0) : d335749 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d333883, d335749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333883, d335749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333690 q = 0) : d335627 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d333690, d335627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34785 q selected
    | true =>
      simp only [d333690, d335627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333691 q = 0) : d335628 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d333691, d335628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333691, d335628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333692 q = 0) : d335629 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d333692, d335629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333692, d335629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d333884 q = 0) : d335750 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d333884, d335750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333884, d335750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333693 q = 0) : d335630 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d333693, d335630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333693, d335630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d333885 q = 0) : d335751 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d333885, d335751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333885, d335751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333886 q = 0) : d335752 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d333886, d335752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d333886, d335752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro34820 (p : Pattern) (selected : d333892 p = 0) : d335758 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333887 q = 0) : d335753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333887, d335753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34819 q selected
    | true =>
      simp only [d333887, d335753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333888 q = 0) : d335754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333888, d335754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333888, d335754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333696 q = 0) : d335633 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333696, d335633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34786 q selected
    | true =>
      simp only [d333696, d335633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333697 q = 0) : d335634 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333697, d335634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333697, d335634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333889 q = 0) : d335755 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333889, d335755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333889, d335755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333890 q = 0) : d335756 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333890, d335756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333890, d335756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333891 q = 0) : d335757 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333891, d335757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333891, d335757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d333892 q = 0) : d335758 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333892, d335758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333892, d335758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro34821 (p : Pattern) (selected : d333898 p = 0) : d335911 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333677 q = 0) : d335753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333677, d335753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34783 q selected
    | true =>
      simp only [d333677, d335753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333678 q = 0) : d335754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333678, d335754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333678, d335754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333895 q = 0) : d335908 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333895, d335908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333895, d335908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333896 q = 0) : d335909 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333896, d335909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333896, d335909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333897 q = 0) : d335910 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333897, d335910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333897, d335910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333898 q = 0) : d335911 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333898, d335911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333898, d335911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34822 (p : Pattern) (selected : d333904 p = 0) : d335917 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333874 q = 0) : d335906 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333874, d335906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34817 q selected
    | true =>
      simp only [d333874, d335906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34784 q selected
  have h2 (q : Pattern) (selected : d333893 q = 0) : d335759 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333893, d335759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34820 q selected
    | true =>
      simp only [d333893, d335759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34787 q selected
  have h3 (q : Pattern) (selected : d333894 q = 0) : d335907 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333894, d335907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333894, d335907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333899 q = 0) : d335912 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333899, d335912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34821 q selected
    | true =>
      simp only [d333899, d335912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333900 q = 0) : d335913 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333900, d335913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333900, d335913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333901 q = 0) : d335914 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333901, d335914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333901, d335914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d333902 q = 0) : d335915 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333902, d335915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333902, d335915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333903 q = 0) : d335916 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333903, d335916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333903, d335916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d333904 q = 0) : d335917 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333904, d335917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333904, d335917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro34823 (p : Pattern) (selected : d333910 p = 0) : d335923 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333538 q = 0) : d335639 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333538, d335639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34759 q selected
    | true =>
      simp only [d333538, d335639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333906 q = 0) : d335919 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333906, d335919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333906, d335919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333907 q = 0) : d335920 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333907, d335920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333907, d335920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333908 q = 0) : d335921 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333908, d335921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333908, d335921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333909 q = 0) : d335922 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333909, d335922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333909, d335922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333910 q = 0) : d335923 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333910, d335923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333910, d335923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro34824 (p : Pattern) (selected : d333916 p = 0) : d335929 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333725 q = 0) : d335782 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333725, d335782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333725, d335782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34791 q selected
  have h2 (q : Pattern) (selected : d333726 q = 0) : d335783 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333726, d335783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333726, d335783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333732 q = 0) : d335789 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333732, d335789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34791 q selected
    | true =>
      simp only [d333732, d335789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34792 q selected
  have h4 (q : Pattern) (selected : d333733 q = 0) : d335790 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333733, d335790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333733, d335790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333734 q = 0) : d335791 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333734, d335791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333734, d335791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333833 q = 0) : d335865 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333833, d335865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34805 q selected
    | true =>
      simp only [d333833, d335865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34811 q selected
  have h7 (q : Pattern) (selected : d333835 q = 0) : d335867 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333835, d335867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34812 q selected
    | true =>
      simp only [d333835, d335867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34763 q selected
  have h8 (q : Pattern) (selected : d333836 q = 0) : d335868 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333836, d335868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333836, d335868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d333837 q = 0) : d335869 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333837, d335869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d333837, d335869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d333838 q = 0) : d335870 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333838, d335870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333838, d335870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d333842 q = 0) : d335874 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333842, d335874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333842, d335874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34813 q selected
  have h12 (q : Pattern) (selected : d333844 q = 0) : d335876 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333844, d335876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333844, d335876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34814 q selected
  have h13 (q : Pattern) (selected : d333845 q = 0) : d335877 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333845, d335877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d333845, d335877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d333846 q = 0) : d335878 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333846, d335878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d333846, d335878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d333847 q = 0) : d335879 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333847, d335879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d333847, d335879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d333848 q = 0) : d335880 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d333848, d335880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d333848, d335880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d333905 q = 0) : d335918 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333905, d335918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333905, d335918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34822 q selected
  have h18 (q : Pattern) (selected : d333911 q = 0) : d335924 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333911, d335924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333911, d335924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34823 q selected
  have h19 (q : Pattern) (selected : d333912 q = 0) : d335925 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333912, d335925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d333912, d335925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d333913 q = 0) : d335926 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333913, d335926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d333913, d335926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d333914 q = 0) : d335927 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d333914, d335927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d333914, d335927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d333915 q = 0) : d335928 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d333915, d335928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d333915, d335928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d333916 q = 0) : d335929 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d333916, d335929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d333916, d335929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro34825 (p : Pattern) (selected : d333922 p = 0) : d335935 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333917 q = 0) : d335930 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d333917, d335930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333917, d335930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34824 q selected
  have h2 (q : Pattern) (selected : d333918 q = 0) : d335931 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d333918, d335931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333918, d335931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333919 q = 0) : d335932 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d333919, d335932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333919, d335932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333920 q = 0) : d335933 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d333920, d335933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333920, d335933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333921 q = 0) : d335934 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d333921, d335934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333921, d335934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333922 q = 0) : d335935 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d333922, d335935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333922, d335935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro34826 (p : Pattern) (selected : d333925 p = 0) : d335938 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333751 q = 0) : d335808 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333751, d335808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34795 q selected
    | true =>
      simp only [d333751, d335808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333752 q = 0) : d335809 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333752, d335809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333752, d335809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333753 q = 0) : d335810 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333753, d335810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333753, d335810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333754 q = 0) : d335811 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333754, d335811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333754, d335811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333756 q = 0) : d335813 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333756, d335813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34796 q selected
    | true =>
      simp only [d333756, d335813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333757 q = 0) : d335814 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333757, d335814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333757, d335814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333758 q = 0) : d335815 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333758, d335815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333758, d335815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333759 q = 0) : d335816 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333759, d335816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333759, d335816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d333760 q = 0) : d335817 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d333760, d335817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333760, d335817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333479 q = 0) : d335580 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333479, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34749 q selected
    | true =>
      simp only [d333479, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d333480 q = 0) : d335581 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333480, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d333480, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d333481 q = 0) : d335582 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333481, d335582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333481, d335582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d333482 q = 0) : d335583 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333482, d335583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d333482, d335583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d333924 q = 0) : d335937 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d333924, d335937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333924, d335937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d333925 q = 0) : d335938 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d333925, d335938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d333925, d335938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro34827 (p : Pattern) (selected : d333926 p = 0) : d335939 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333586 q = 0) : d335687 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333586, d335687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34766 q selected
    | true =>
      simp only [d333586, d335687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333587 q = 0) : d335688 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333587, d335688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333587, d335688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333588 q = 0) : d335689 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333588, d335689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333588, d335689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333589 q = 0) : d335690 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333589, d335690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333589, d335690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333479 q = 0) : d335580 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333479, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34749 q selected
    | true =>
      simp only [d333479, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333480 q = 0) : d335581 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333480, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333480, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333481 q = 0) : d335582 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333481, d335582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333481, d335582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333482 q = 0) : d335583 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333482, d335583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333482, d335583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d333590 q = 0) : d335691 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d333590, d335691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333590, d335691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333483 q = 0) : d335584 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d333483, d335584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d333483, d335584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d333926 q = 0) : d335939 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d333926, d335939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d333926, d335939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro34828 (p : Pattern) (selected : d333936 p = 0) : d335949 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333927 q = 0) : d335940 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d333927, d335940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34826 q selected
    | true =>
      simp only [d333927, d335940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34827 q selected
  have h2 (q : Pattern) (selected : d333928 q = 0) : d335941 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d333928, d335941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333928, d335941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333929 q = 0) : d335942 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d333929, d335942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333929, d335942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333930 q = 0) : d335943 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d333930, d335943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34827 q selected
    | true =>
      simp only [d333930, d335943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34750 q selected
  have h5 (q : Pattern) (selected : d333931 q = 0) : d335944 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d333931, d335944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333931, d335944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333932 q = 0) : d335945 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d333932, d335945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333932, d335945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d333933 q = 0) : d335946 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d333933, d335946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333933, d335946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333934 q = 0) : d335947 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d333934, d335947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333934, d335947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d333935 q = 0) : d335948 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d333935, d335948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333935, d335948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333936 q = 0) : d335949 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d333936, d335949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d333936, d335949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro34829 (p : Pattern) (selected : d333940 p = 0) : d335953 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333930 q = 0) : d335943 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d333930, d335943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34827 q selected
    | true =>
      simp only [d333930, d335943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34750 q selected
  have h2 (q : Pattern) (selected : d333931 q = 0) : d335944 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d333931, d335944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333931, d335944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333932 q = 0) : d335945 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d333932, d335945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333932, d335945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333934 q = 0) : d335947 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d333934, d335947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333934, d335947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333939 q = 0) : d335952 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d333939, d335952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333939, d335952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333940 q = 0) : d335953 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d333940, d335953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333940, d335953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34830 (p : Pattern) (selected : d333946 p = 0) : d335959 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333937 q = 0) : d335950 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333937, d335950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34828 q selected
    | true =>
      simp only [d333937, d335950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333938 q = 0) : d335951 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333938, d335951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333938, d335951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333941 q = 0) : d335954 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333941, d335954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34829 q selected
    | true =>
      simp only [d333941, d335954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333942 q = 0) : d335955 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333942, d335955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333942, d335955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333943 q = 0) : d335956 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333943, d335956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333943, d335956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333944 q = 0) : d335957 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333944, d335957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333944, d335957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333945 q = 0) : d335958 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333945, d335958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333945, d335958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d333946 q = 0) : d335959 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333946, d335959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333946, d335959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro34831 (p : Pattern) (selected : d333950 p = 0) : d335963 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333941 q = 0) : d335954 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333941, d335954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34829 q selected
    | true =>
      simp only [d333941, d335954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333942 q = 0) : d335955 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333942, d335955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333942, d335955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333947 q = 0) : d335960 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333947, d335960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333947, d335960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333948 q = 0) : d335961 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333948, d335961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333948, d335961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333949 q = 0) : d335962 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333949, d335962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333949, d335962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333950 q = 0) : d335963 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333950, d335963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333950, d335963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro34832 (p : Pattern) (selected : d333956 p = 0) : d335969 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333951 q = 0) : d335964 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333951, d335964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34830 q selected
    | true =>
      simp only [d333951, d335964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34831 q selected
  have h2 (q : Pattern) (selected : d333952 q = 0) : d335965 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333952, d335965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333952, d335965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333953 q = 0) : d335966 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333953, d335966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333953, d335966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333954 q = 0) : d335967 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333954, d335967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333954, d335967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333955 q = 0) : d335968 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333955, d335968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333955, d335968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333956 q = 0) : d335969 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333956, d335969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333956, d335969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro34833 (p : Pattern) (selected : d333959 p = 0) : d335972 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333937 q = 0) : d335950 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333937, d335950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34828 q selected
    | true =>
      simp only [d333937, d335950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333938 q = 0) : d335951 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333938, d335951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333938, d335951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333941 q = 0) : d335954 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333941, d335954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34829 q selected
    | true =>
      simp only [d333941, d335954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333942 q = 0) : d335955 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333942, d335955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333942, d335955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333943 q = 0) : d335956 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333943, d335956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333943, d335956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333944 q = 0) : d335957 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333944, d335957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333944, d335957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333945 q = 0) : d335958 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333945, d335958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333945, d335958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d333959 q = 0) : d335972 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333959, d335972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333959, d335972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro34834 (p : Pattern) (selected : d333960 p = 0) : d335973 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333941 q = 0) : d335954 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333941, d335954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34829 q selected
    | true =>
      simp only [d333941, d335954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333942 q = 0) : d335955 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333942, d335955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333942, d335955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333947 q = 0) : d335960 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333947, d335960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333947, d335960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333948 q = 0) : d335961 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333948, d335961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333948, d335961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333949 q = 0) : d335962 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333949, d335962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333949, d335962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333960 q = 0) : d335973 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333960, d335973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333960, d335973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34835 (p : Pattern) (selected : d333966 p = 0) : d335979 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333951 q = 0) : d335964 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333951, d335964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34830 q selected
    | true =>
      simp only [d333951, d335964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34831 q selected
  have h2 (q : Pattern) (selected : d333952 q = 0) : d335965 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333952, d335965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333952, d335965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333953 q = 0) : d335966 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333953, d335966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333953, d335966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333954 q = 0) : d335967 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333954, d335967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333954, d335967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333955 q = 0) : d335968 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333955, d335968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333955, d335968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333961 q = 0) : d335974 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333961, d335974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34833 q selected
    | true =>
      simp only [d333961, d335974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34834 q selected
  have h7 (q : Pattern) (selected : d333962 q = 0) : d335975 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333962, d335975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333962, d335975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333963 q = 0) : d335976 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333963, d335976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333963, d335976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d333964 q = 0) : d335977 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333964, d335977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333964, d335977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333965 q = 0) : d335978 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333965, d335978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333965, d335978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d333966 q = 0) : d335979 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d333966, d335979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333966, d335979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro34836 (p : Pattern) (selected : d333971 p = 0) : d335984 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333937 q = 0) : d335950 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333937, d335950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34828 q selected
    | true =>
      simp only [d333937, d335950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333938 q = 0) : d335951 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333938, d335951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333938, d335951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333941 q = 0) : d335954 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333941, d335954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34829 q selected
    | true =>
      simp only [d333941, d335954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333942 q = 0) : d335955 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333942, d335955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333942, d335955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333943 q = 0) : d335956 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333943, d335956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333943, d335956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333944 q = 0) : d335957 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333944, d335957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333944, d335957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333970 q = 0) : d335983 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333970, d335983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333970, d335983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333971 q = 0) : d335984 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333971, d335984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333971, d335984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro34837 (p : Pattern) (selected : d333973 p = 0) : d335986 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333941 q = 0) : d335954 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333941, d335954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34829 q selected
    | true =>
      simp only [d333941, d335954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333942 q = 0) : d335955 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333942, d335955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333942, d335955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333947 q = 0) : d335960 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333947, d335960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333947, d335960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333948 q = 0) : d335961 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333948, d335961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333948, d335961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333972 q = 0) : d335985 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333972, d335985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333972, d335985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333973 q = 0) : d335986 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333973, d335986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333973, d335986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro34838 (p : Pattern) (selected : d333980 p = 0) : d335993 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333937 q = 0) : d335950 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333937, d335950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34828 q selected
    | true =>
      simp only [d333937, d335950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333938 q = 0) : d335951 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333938, d335951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333938, d335951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333941 q = 0) : d335954 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333941, d335954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34829 q selected
    | true =>
      simp only [d333941, d335954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333942 q = 0) : d335955 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333942, d335955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333942, d335955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333943 q = 0) : d335956 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333943, d335956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333943, d335956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333978 q = 0) : d335991 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333978, d335991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333978, d335991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d333979 q = 0) : d335992 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333979, d335992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333979, d335992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d333980 q = 0) : d335993 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333980, d335993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333980, d335993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro34839 (p : Pattern) (selected : d333983 p = 0) : d335996 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333941 q = 0) : d335954 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333941, d335954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34829 q selected
    | true =>
      simp only [d333941, d335954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333942 q = 0) : d335955 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333942, d335955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333942, d335955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333947 q = 0) : d335960 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333947, d335960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333947, d335960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333981 q = 0) : d335994 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333981, d335994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333981, d335994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333982 q = 0) : d335995 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333982, d335995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333982, d335995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333983 q = 0) : d335996 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d333983, d335996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333983, d335996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro34840 (p : Pattern) (selected : d333993 p = 0) : d336006 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333987 q = 0) : d336000 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333987, d336000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23519 q selected
    | true =>
      simp only [d333987, d336000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333988 q = 0) : d336001 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333988, d336001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23520 q selected
    | true =>
      simp only [d333988, d336001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333989 q = 0) : d336002 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d333989, d336002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333989, d336002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333990 q = 0) : d336003 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d333990, d336003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333990, d336003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333582 q = 0) : d335683 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333582, d335683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro204 q selected
    | true =>
      simp only [d333582, d335683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333991 q = 0) : d336004 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d333991, d336004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333991, d336004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d333992 q = 0) : d336005 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d333992, d336005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333992, d336005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d333993 q = 0) : d336006 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d333993, d336006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333993, d336006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro34841 (p : Pattern) (selected : d333998 p = 0) : d336011 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333747 q = 0) : d335804 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333747, d335804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23495 q selected
    | true =>
      simp only [d333747, d335804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333582 q = 0) : d335683 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333582, d335683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro204 q selected
    | true =>
      simp only [d333582, d335683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333748 q = 0) : d335805 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d333748, d335805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333748, d335805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333749 q = 0) : d335806 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d333749, d335806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333749, d335806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333998 q = 0) : d336011 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d333998, d336011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333998, d336011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro34842 (p : Pattern) (selected : d334004 p = 0) : d336017 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333994 q = 0) : d336007 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333994, d336007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34840 q selected
    | true =>
      simp only [d333994, d336007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333995 q = 0) : d336008 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333995, d336008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333995, d336008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333996 q = 0) : d336009 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333996, d336009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333996, d336009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333997 q = 0) : d336010 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333997, d336010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333997, d336010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333999 q = 0) : d336012 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333999, d336012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34841 q selected
    | true =>
      simp only [d333999, d336012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334000 q = 0) : d336013 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334000, d336013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334000, d336013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334001 q = 0) : d336014 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334001, d336014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334001, d336014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334002 q = 0) : d336015 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334002, d336015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334002, d336015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334003 q = 0) : d336016 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334003, d336016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334003, d336016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334004 q = 0) : d336017 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334004, d336017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334004, d336017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro34843 (p : Pattern) (selected : d334008 p = 0) : d336021 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333479 q = 0) : d335580 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333479, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34749 q selected
    | true =>
      simp only [d333479, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333480 q = 0) : d335581 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333480, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333480, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333481 q = 0) : d335582 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333481, d335582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333481, d335582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333482 q = 0) : d335583 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333482, d335583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333482, d335583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333924 q = 0) : d335937 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d333924, d335937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333924, d335937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333483 q = 0) : d335584 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d333483, d335584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333483, d335584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334008 q = 0) : d336021 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334008, d336021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334008, d336021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro34844 (p : Pattern) (selected : d334014 p = 0) : d336027 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334005 q = 0) : d336018 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334005, d336018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34842 q selected
    | true =>
      simp only [d334005, d336018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34826 q selected
  have h2 (q : Pattern) (selected : d334006 q = 0) : d336019 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334006, d336019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334006, d336019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334007 q = 0) : d336020 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334007, d336020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334007, d336020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334009 q = 0) : d336022 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334009, d336022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34826 q selected
    | true =>
      simp only [d334009, d336022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34843 q selected
  have h5 (q : Pattern) (selected : d334010 q = 0) : d336023 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334010, d336023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334010, d336023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334011 q = 0) : d336024 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334011, d336024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334011, d336024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334012 q = 0) : d336025 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334012, d336025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334012, d336025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333927 q = 0) : d335940 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d333927, d335940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34826 q selected
    | true =>
      simp only [d333927, d335940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34827 q selected
  have h9 (q : Pattern) (selected : d333928 q = 0) : d335941 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d333928, d335941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333928, d335941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333929 q = 0) : d335942 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d333929, d335942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333929, d335942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d333930 q = 0) : d335943 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d333930, d335943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34827 q selected
    | true =>
      simp only [d333930, d335943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34750 q selected
  have h12 (q : Pattern) (selected : d333931 q = 0) : d335944 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d333931, d335944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333931, d335944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d333932 q = 0) : d335945 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d333932, d335945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333932, d335945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d333933 q = 0) : d335946 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d333933, d335946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d333933, d335946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d334013 q = 0) : d336026 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334013, d336026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334013, d336026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d334014 q = 0) : d336027 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334014, d336027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d334014, d336027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro34845 (p : Pattern) (selected : d334020 p = 0) : d336033 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334015 q = 0) : d336028 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334015, d336028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34844 q selected
    | true =>
      simp only [d334015, d336028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334016 q = 0) : d336029 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334016, d336029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334016, d336029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333937 q = 0) : d335950 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333937, d335950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34828 q selected
    | true =>
      simp only [d333937, d335950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333938 q = 0) : d335951 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333938, d335951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333938, d335951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334017 q = 0) : d336030 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334017, d336030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334017, d336030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334018 q = 0) : d336031 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334018, d336031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334018, d336031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334019 q = 0) : d336032 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334019, d336032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334019, d336032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334020 q = 0) : d336033 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334020, d336033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334020, d336033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro34846 (p : Pattern) (selected : d334025 p = 0) : d335807 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334022 q = 0) : d335804 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334022, d335804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23527 q selected
    | true =>
      simp only [d334022, d335804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333778 q = 0) : d335683 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333778, d335683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro239 q selected
    | true =>
      simp only [d333778, d335683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334023 q = 0) : d335805 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334023, d335805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334023, d335805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334024 q = 0) : d335806 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334024, d335806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334024, d335806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333605 q = 0) : d335576 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333605, d335576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
    | true =>
      simp only [d333605, d335576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333779 q = 0) : d335684 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d333779, d335684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333779, d335684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d333780 q = 0) : d335685 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d333780, d335685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333780, d335685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334025 q = 0) : d335807 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d334025, d335807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334025, d335807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro34847 (p : Pattern) (selected : d334030 p = 0) : d335812 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333778 q = 0) : d335683 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333778, d335683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro239 q selected
    | true =>
      simp only [d333778, d335683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333605 q = 0) : d335576 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333605, d335576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
    | true =>
      simp only [d333605, d335576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333779 q = 0) : d335684 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d333779, d335684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333779, d335684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333780 q = 0) : d335685 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d333780, d335685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333780, d335685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334030 q = 0) : d335812 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d334030, d335812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334030, d335812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro34848 (p : Pattern) (selected : d334037 p = 0) : d335938 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334026 q = 0) : d335808 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334026, d335808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34846 q selected
    | true =>
      simp only [d334026, d335808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334027 q = 0) : d335809 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334027, d335809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334027, d335809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334028 q = 0) : d335810 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334028, d335810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334028, d335810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334029 q = 0) : d335811 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334029, d335811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334029, d335811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334031 q = 0) : d335813 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334031, d335813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34847 q selected
    | true =>
      simp only [d334031, d335813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334032 q = 0) : d335814 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334032, d335814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334032, d335814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334033 q = 0) : d335815 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334033, d335815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334033, d335815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334034 q = 0) : d335816 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334034, d335816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334034, d335816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334035 q = 0) : d335817 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334035, d335817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334035, d335817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333609 q = 0) : d335580 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333609, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34770 q selected
    | true =>
      simp only [d333609, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d333610 q = 0) : d335581 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333610, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d333610, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d333611 q = 0) : d335582 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333611, d335582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333611, d335582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d333612 q = 0) : d335583 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333612, d335583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d333612, d335583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d334036 q = 0) : d335937 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334036, d335937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334036, d335937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d334037 q = 0) : d335938 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334037, d335938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334037, d335938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro34849 (p : Pattern) (selected : d334038 p = 0) : d335939 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333782 q = 0) : d335687 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333782, d335687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34800 q selected
    | true =>
      simp only [d333782, d335687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333783 q = 0) : d335688 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333783, d335688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333783, d335688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333784 q = 0) : d335689 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333784, d335689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333784, d335689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333785 q = 0) : d335690 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333785, d335690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333785, d335690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333609 q = 0) : d335580 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333609, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34770 q selected
    | true =>
      simp only [d333609, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333610 q = 0) : d335581 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333610, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333610, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333611 q = 0) : d335582 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333611, d335582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333611, d335582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333612 q = 0) : d335583 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333612, d335583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333612, d335583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d333786 q = 0) : d335691 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d333786, d335691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333786, d335691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333613 q = 0) : d335584 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d333613, d335584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d333613, d335584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d334038 q = 0) : d335939 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334038, d335939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334038, d335939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro34850 (p : Pattern) (selected : d334048 p = 0) : d335949 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334039 q = 0) : d335940 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334039, d335940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34848 q selected
    | true =>
      simp only [d334039, d335940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34849 q selected
  have h2 (q : Pattern) (selected : d334040 q = 0) : d335941 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334040, d335941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334040, d335941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334041 q = 0) : d335942 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334041, d335942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334041, d335942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334042 q = 0) : d335943 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334042, d335943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34849 q selected
    | true =>
      simp only [d334042, d335943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34771 q selected
  have h5 (q : Pattern) (selected : d334043 q = 0) : d335944 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334043, d335944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334043, d335944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334044 q = 0) : d335945 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334044, d335945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334044, d335945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334045 q = 0) : d335946 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334045, d335946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334045, d335946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334046 q = 0) : d335947 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334046, d335947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334046, d335947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334047 q = 0) : d335948 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334047, d335948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334047, d335948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334048 q = 0) : d335949 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334048, d335949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334048, d335949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro34851 (p : Pattern) (selected : d334052 p = 0) : d335953 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334042 q = 0) : d335943 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334042, d335943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34849 q selected
    | true =>
      simp only [d334042, d335943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34771 q selected
  have h2 (q : Pattern) (selected : d334043 q = 0) : d335944 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334043, d335944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334043, d335944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334044 q = 0) : d335945 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334044, d335945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334044, d335945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334046 q = 0) : d335947 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334046, d335947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334046, d335947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334051 q = 0) : d335952 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334051, d335952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334051, d335952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334052 q = 0) : d335953 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334052, d335953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334052, d335953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34852 (p : Pattern) (selected : d334058 p = 0) : d335959 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334049 q = 0) : d335950 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334049, d335950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34850 q selected
    | true =>
      simp only [d334049, d335950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334050 q = 0) : d335951 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334050, d335951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334050, d335951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334053 q = 0) : d335954 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334053, d335954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34851 q selected
    | true =>
      simp only [d334053, d335954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334054 q = 0) : d335955 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334054, d335955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334054, d335955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334055 q = 0) : d335956 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334055, d335956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334055, d335956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334056 q = 0) : d335957 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334056, d335957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334056, d335957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334057 q = 0) : d335958 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334057, d335958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334057, d335958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334058 q = 0) : d335959 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334058, d335959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334058, d335959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro34853 (p : Pattern) (selected : d334062 p = 0) : d335963 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334053 q = 0) : d335954 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334053, d335954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34851 q selected
    | true =>
      simp only [d334053, d335954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334054 q = 0) : d335955 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334054, d335955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334054, d335955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334059 q = 0) : d335960 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334059, d335960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334059, d335960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334060 q = 0) : d335961 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334060, d335961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334060, d335961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334061 q = 0) : d335962 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334061, d335962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334061, d335962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334062 q = 0) : d335963 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334062, d335963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334062, d335963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro34854 (p : Pattern) (selected : d334068 p = 0) : d336039 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333937 q = 0) : d335950 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333937, d335950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34828 q selected
    | true =>
      simp only [d333937, d335950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333938 q = 0) : d335951 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333938, d335951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333938, d335951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334065 q = 0) : d336036 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334065, d336036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334065, d336036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334066 q = 0) : d336037 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334066, d336037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334066, d336037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334067 q = 0) : d336038 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334067, d336038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334067, d336038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334068 q = 0) : d336039 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334068, d336039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334068, d336039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro34855 (p : Pattern) (selected : d334074 p = 0) : d336045 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333974 q = 0) : d335987 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333974, d335987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34836 q selected
    | true =>
      simp only [d333974, d335987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34837 q selected
  have h2 (q : Pattern) (selected : d333975 q = 0) : d335988 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333975, d335988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333975, d335988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333976 q = 0) : d335989 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333976, d335989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333976, d335989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333977 q = 0) : d335990 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333977, d335990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333977, d335990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333984 q = 0) : d335997 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333984, d335997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34838 q selected
    | true =>
      simp only [d333984, d335997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34839 q selected
  have h6 (q : Pattern) (selected : d333985 q = 0) : d335998 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333985, d335998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333985, d335998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d333986 q = 0) : d335999 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333986, d335999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333986, d335999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334021 q = 0) : d336034 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334021, d336034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34845 q selected
    | true =>
      simp only [d334021, d336034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34830 q selected
  have h9 (q : Pattern) (selected : d334063 q = 0) : d335964 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334063, d335964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34852 q selected
    | true =>
      simp only [d334063, d335964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34853 q selected
  have h10 (q : Pattern) (selected : d334064 q = 0) : d336035 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334064, d336035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d334064, d336035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d334069 q = 0) : d336040 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334069, d336040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34854 q selected
    | true =>
      simp only [d334069, d336040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d334070 q = 0) : d336041 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334070, d336041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d334070, d336041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d334071 q = 0) : d336042 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334071, d336042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d334071, d336042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d334072 q = 0) : d336043 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334072, d336043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334072, d336043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d334073 q = 0) : d336044 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334073, d336044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334073, d336044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d334074 q = 0) : d336045 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d334074, d336045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334074, d336045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro34856 (p : Pattern) (selected : d334075 p = 0) : d336046 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333937 q = 0) : d335950 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333937, d335950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34828 q selected
    | true =>
      simp only [d333937, d335950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333938 q = 0) : d335951 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333938, d335951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333938, d335951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333941 q = 0) : d335954 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333941, d335954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34829 q selected
    | true =>
      simp only [d333941, d335954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333942 q = 0) : d335955 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333942, d335955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333942, d335955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333943 q = 0) : d335956 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333943, d335956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333943, d335956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333944 q = 0) : d335957 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333944, d335957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333944, d335957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333970 q = 0) : d335983 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333970, d335983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333970, d335983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334075 q = 0) : d336046 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334075, d336046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334075, d336046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro34857 (p : Pattern) (selected : d334076 p = 0) : d336047 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333941 q = 0) : d335954 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333941, d335954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34829 q selected
    | true =>
      simp only [d333941, d335954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333942 q = 0) : d335955 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333942, d335955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333942, d335955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333947 q = 0) : d335960 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333947, d335960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333947, d335960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333948 q = 0) : d335961 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333948, d335961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333948, d335961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333972 q = 0) : d335985 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333972, d335985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333972, d335985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334076 q = 0) : d336047 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334076, d336047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334076, d336047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34858 (p : Pattern) (selected : d334081 p = 0) : d336052 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333937 q = 0) : d335950 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333937, d335950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34828 q selected
    | true =>
      simp only [d333937, d335950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333938 q = 0) : d335951 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333938, d335951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333938, d335951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333941 q = 0) : d335954 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333941, d335954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34829 q selected
    | true =>
      simp only [d333941, d335954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333942 q = 0) : d335955 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333942, d335955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333942, d335955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333943 q = 0) : d335956 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333943, d335956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333943, d335956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333978 q = 0) : d335991 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333978, d335991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333978, d335991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d333979 q = 0) : d335992 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333979, d335992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333979, d335992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334081 q = 0) : d336052 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334081, d336052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334081, d336052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro34859 (p : Pattern) (selected : d334082 p = 0) : d336053 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333941 q = 0) : d335954 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333941, d335954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34829 q selected
    | true =>
      simp only [d333941, d335954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333942 q = 0) : d335955 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333942, d335955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333942, d335955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333947 q = 0) : d335960 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333947, d335960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333947, d335960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333981 q = 0) : d335994 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d333981, d335994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333981, d335994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333982 q = 0) : d335995 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d333982, d335995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333982, d335995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334082 q = 0) : d336053 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334082, d336053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334082, d336053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34860 (p : Pattern) (selected : d334086 p = 0) : d336057 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334015 q = 0) : d336028 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334015, d336028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34844 q selected
    | true =>
      simp only [d334015, d336028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334016 q = 0) : d336029 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334016, d336029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334016, d336029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333937 q = 0) : d335950 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333937, d335950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34828 q selected
    | true =>
      simp only [d333937, d335950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333938 q = 0) : d335951 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333938, d335951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333938, d335951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334017 q = 0) : d336030 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334017, d336030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334017, d336030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334018 q = 0) : d336031 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334018, d336031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334018, d336031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334019 q = 0) : d336032 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334019, d336032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334019, d336032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334086 q = 0) : d336057 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334086, d336057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334086, d336057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro34861 (p : Pattern) (selected : d334088 p = 0) : d335972 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334049 q = 0) : d335950 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334049, d335950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34850 q selected
    | true =>
      simp only [d334049, d335950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334050 q = 0) : d335951 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334050, d335951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334050, d335951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334053 q = 0) : d335954 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334053, d335954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34851 q selected
    | true =>
      simp only [d334053, d335954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334054 q = 0) : d335955 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334054, d335955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334054, d335955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334055 q = 0) : d335956 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334055, d335956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334055, d335956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334056 q = 0) : d335957 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334056, d335957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334056, d335957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334057 q = 0) : d335958 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334057, d335958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334057, d335958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334088 q = 0) : d335972 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334088, d335972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334088, d335972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro34862 (p : Pattern) (selected : d334089 p = 0) : d335973 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334053 q = 0) : d335954 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334053, d335954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34851 q selected
    | true =>
      simp only [d334053, d335954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334054 q = 0) : d335955 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334054, d335955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334054, d335955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334059 q = 0) : d335960 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334059, d335960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334059, d335960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334060 q = 0) : d335961 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334060, d335961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334060, d335961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334061 q = 0) : d335962 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334061, d335962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334061, d335962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334089 q = 0) : d335973 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334089, d335973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334089, d335973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34863 (p : Pattern) (selected : d334092 p = 0) : d336060 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333937 q = 0) : d335950 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d333937, d335950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34828 q selected
    | true =>
      simp only [d333937, d335950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333938 q = 0) : d335951 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d333938, d335951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333938, d335951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334065 q = 0) : d336036 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334065, d336036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334065, d336036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334066 q = 0) : d336037 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334066, d336037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334066, d336037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334067 q = 0) : d336038 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334067, d336038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334067, d336038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334092 q = 0) : d336060 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334092, d336060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334092, d336060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34864 (p : Pattern) (selected : d334098 p = 0) : d336066 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333974 q = 0) : d335987 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333974, d335987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34836 q selected
    | true =>
      simp only [d333974, d335987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34837 q selected
  have h2 (q : Pattern) (selected : d333975 q = 0) : d335988 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333975, d335988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333975, d335988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333976 q = 0) : d335989 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333976, d335989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333976, d335989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333977 q = 0) : d335990 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333977, d335990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333977, d335990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333984 q = 0) : d335997 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333984, d335997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34838 q selected
    | true =>
      simp only [d333984, d335997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34839 q selected
  have h6 (q : Pattern) (selected : d333985 q = 0) : d335998 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333985, d335998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333985, d335998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d333986 q = 0) : d335999 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333986, d335999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333986, d335999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334021 q = 0) : d336034 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334021, d336034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34845 q selected
    | true =>
      simp only [d334021, d336034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34830 q selected
  have h9 (q : Pattern) (selected : d334063 q = 0) : d335964 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334063, d335964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34852 q selected
    | true =>
      simp only [d334063, d335964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34853 q selected
  have h10 (q : Pattern) (selected : d334064 q = 0) : d336035 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334064, d336035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d334064, d336035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d334069 q = 0) : d336040 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334069, d336040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34854 q selected
    | true =>
      simp only [d334069, d336040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d334070 q = 0) : d336041 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334070, d336041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d334070, d336041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d334071 q = 0) : d336042 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334071, d336042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d334071, d336042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d334072 q = 0) : d336043 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334072, d336043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334072, d336043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d334073 q = 0) : d336044 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334073, d336044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334073, d336044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d334077 q = 0) : d336048 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334077, d336048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34856 q selected
    | true =>
      simp only [d334077, d336048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34857 q selected
  have h17 (q : Pattern) (selected : d334078 q = 0) : d336049 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334078, d336049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334078, d336049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d334079 q = 0) : d336050 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334079, d336050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d334079, d336050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d334080 q = 0) : d336051 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334080, d336051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334080, d336051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d334083 q = 0) : d336054 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334083, d336054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34858 q selected
    | true =>
      simp only [d334083, d336054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34859 q selected
  have h21 (q : Pattern) (selected : d334084 q = 0) : d336055 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334084, d336055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334084, d336055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d334085 q = 0) : d336056 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334085, d336056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d334085, d336056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d334087 q = 0) : d336058 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334087, d336058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34860 q selected
    | true =>
      simp only [d334087, d336058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34833 q selected
  have h24 (q : Pattern) (selected : d334090 q = 0) : d335974 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334090, d335974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34861 q selected
    | true =>
      simp only [d334090, d335974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34862 q selected
  have h25 (q : Pattern) (selected : d334091 q = 0) : d336059 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334091, d336059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d334091, d336059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d334093 q = 0) : d336061 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334093, d336061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34863 q selected
    | true =>
      simp only [d334093, d336061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d334094 q = 0) : d336062 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334094, d336062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d334094, d336062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d334095 q = 0) : d336063 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334095, d336063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d334095, d336063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d334096 q = 0) : d336064 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334096, d336064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d334096, d336064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d334097 q = 0) : d336065 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334097, d336065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d334097, d336065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d334098 q = 0) : d336066 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d334098, d336066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d334098, d336066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro34865 (p : Pattern) (selected : d334105 p = 0) : d336073 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333951 q = 0) : d335964 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d333951, d335964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34830 q selected
    | true =>
      simp only [d333951, d335964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34831 q selected
  have h2 (q : Pattern) (selected : d333952 q = 0) : d335965 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d333952, d335965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333952, d335965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d333953 q = 0) : d335966 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d333953, d335966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333953, d335966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333954 q = 0) : d335967 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d333954, d335967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333954, d335967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333955 q = 0) : d335968 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d333955, d335968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333955, d335968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334100 q = 0) : d336068 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334100, d336068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34831 q selected
    | true =>
      simp only [d334100, d336068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334101 q = 0) : d336069 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334101, d336069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334101, d336069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334102 q = 0) : d336070 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334102, d336070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334102, d336070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334103 q = 0) : d336071 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334103, d336071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334103, d336071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334104 q = 0) : d336072 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334104, d336072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334104, d336072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d334105 q = 0) : d336073 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d334105, d336073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334105, d336073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro34866 (p : Pattern) (selected : d334111 p = 0) : d336079 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334100 q = 0) : d336068 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334100, d336068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34831 q selected
    | true =>
      simp only [d334100, d336068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334101 q = 0) : d336069 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334101, d336069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334101, d336069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334102 q = 0) : d336070 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334102, d336070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334102, d336070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334103 q = 0) : d336071 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334103, d336071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334103, d336071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334104 q = 0) : d336072 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334104, d336072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334104, d336072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334106 q = 0) : d336074 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334106, d336074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34834 q selected
    | true =>
      simp only [d334106, d336074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334107 q = 0) : d336075 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334107, d336075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334107, d336075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334108 q = 0) : d336076 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334108, d336076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334108, d336076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334109 q = 0) : d336077 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334109, d336077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334109, d336077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334110 q = 0) : d336078 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334110, d336078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334110, d336078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d334111 q = 0) : d336079 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d334111, d336079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334111, d336079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro34867 (p : Pattern) (selected : d334118 p = 0) : d336086 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334087 q = 0) : d336058 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334087, d336058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34860 q selected
    | true =>
      simp only [d334087, d336058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34833 q selected
  have h2 (q : Pattern) (selected : d334090 q = 0) : d335974 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334090, d335974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34861 q selected
    | true =>
      simp only [d334090, d335974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34862 q selected
  have h3 (q : Pattern) (selected : d334091 q = 0) : d336059 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334091, d336059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334091, d336059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334093 q = 0) : d336061 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334093, d336061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34863 q selected
    | true =>
      simp only [d334093, d336061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334094 q = 0) : d336062 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334094, d336062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334094, d336062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334095 q = 0) : d336063 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334095, d336063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334095, d336063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334116 q = 0) : d336084 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334116, d336084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334116, d336084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334117 q = 0) : d336085 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334117, d336085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334117, d336085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d334118 q = 0) : d336086 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d334118, d336086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334118, d336086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro34868 (p : Pattern) (selected : d334120 p = 0) : d336088 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334106 q = 0) : d336074 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334106, d336074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34834 q selected
    | true =>
      simp only [d334106, d336074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334107 q = 0) : d336075 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334107, d336075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334107, d336075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334108 q = 0) : d336076 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334108, d336076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334108, d336076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334109 q = 0) : d336077 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334109, d336077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334109, d336077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334110 q = 0) : d336078 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334110, d336078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334110, d336078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334120 q = 0) : d336088 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d334120, d336088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334120, d336088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro34869 (p : Pattern) (selected : d334135 p = 0) : d336103 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334126 q = 0) : d336094 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334126, d336094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334126, d336094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34840 q selected
  have h2 (q : Pattern) (selected : d333994 q = 0) : d336007 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333994, d336007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34840 q selected
    | true =>
      simp only [d333994, d336007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334127 q = 0) : d336095 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334127, d336095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334127, d336095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333995 q = 0) : d336008 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333995, d336008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333995, d336008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334128 q = 0) : d336096 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334128, d336096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334128, d336096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334129 q = 0) : d336097 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334129, d336097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334129, d336097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334130 q = 0) : d336098 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334130, d336098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334130, d336098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34841 q selected
  have h8 (q : Pattern) (selected : d333999 q = 0) : d336012 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333999, d336012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34841 q selected
    | true =>
      simp only [d333999, d336012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334131 q = 0) : d336099 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334131, d336099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334131, d336099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334000 q = 0) : d336013 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334000, d336013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d334000, d336013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d334132 q = 0) : d336100 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334132, d336100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334132, d336100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d334133 q = 0) : d336101 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334133, d336101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d334133, d336101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d334134 q = 0) : d336102 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334134, d336102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334134, d336102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d334135 q = 0) : d336103 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334135, d336103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d334135, d336103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h14 p selected
theorem eqIntro34870 (p : Pattern) (selected : d334137 p = 0) : d336105 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333849 q = 0) : d335881 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333849, d335881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333849, d335881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34795 q selected
  have h2 (q : Pattern) (selected : d333751 q = 0) : d335808 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333751, d335808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34795 q selected
    | true =>
      simp only [d333751, d335808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333850 q = 0) : d335882 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333850, d335882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333850, d335882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333752 q = 0) : d335809 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333752, d335809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333752, d335809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333851 q = 0) : d335883 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333851, d335883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333851, d335883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333852 q = 0) : d335884 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333852, d335884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333852, d335884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333853 q = 0) : d335885 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333853, d335885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333853, d335885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34796 q selected
  have h8 (q : Pattern) (selected : d333756 q = 0) : d335813 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333756, d335813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34796 q selected
    | true =>
      simp only [d333756, d335813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d333854 q = 0) : d335886 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333854, d335886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333854, d335886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333757 q = 0) : d335814 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333757, d335814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d333757, d335814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d333855 q = 0) : d335887 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333855, d335887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d333855, d335887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d333856 q = 0) : d335888 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333856, d335888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d333856, d335888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d333857 q = 0) : d335889 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d333857, d335889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333857, d335889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d333520 q = 0) : d335621 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333520, d335621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333520, d335621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34749 q selected
  have h15 (q : Pattern) (selected : d333479 q = 0) : d335580 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333479, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34749 q selected
    | true =>
      simp only [d333479, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d333521 q = 0) : d335622 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333521, d335622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d333521, d335622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d333480 q = 0) : d335581 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333480, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d333480, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d333522 q = 0) : d335623 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333522, d335623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d333522, d335623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d333523 q = 0) : d335624 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333523, d335624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d333523, d335624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d334136 q = 0) : d336104 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334136, d336104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334136, d336104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d334137 q = 0) : d336105 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334137, d336105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d334137, d336105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro34871 (p : Pattern) (selected : d334141 p = 0) : d336109 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333520 q = 0) : d335621 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333520, d335621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333520, d335621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34749 q selected
  have h2 (q : Pattern) (selected : d333479 q = 0) : d335580 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333479, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34749 q selected
    | true =>
      simp only [d333479, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333521 q = 0) : d335622 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333521, d335622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333521, d335622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333480 q = 0) : d335581 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333480, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333480, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333522 q = 0) : d335623 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333522, d335623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333522, d335623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333523 q = 0) : d335624 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333523, d335624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333523, d335624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334136 q = 0) : d336104 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334136, d336104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334136, d336104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333524 q = 0) : d335625 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d333524, d335625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333524, d335625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334141 q = 0) : d336109 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334141, d336109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334141, d336109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro34872 (p : Pattern) (selected : d334146 p = 0) : d336114 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333665 q = 0) : d335741 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333665, d335741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333665, d335741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34766 q selected
  have h2 (q : Pattern) (selected : d333586 q = 0) : d335687 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333586, d335687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34766 q selected
    | true =>
      simp only [d333586, d335687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333666 q = 0) : d335742 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333666, d335742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333666, d335742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333587 q = 0) : d335688 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333587, d335688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333587, d335688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333667 q = 0) : d335743 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333667, d335743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333667, d335743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333668 q = 0) : d335744 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333668, d335744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333668, d335744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333520 q = 0) : d335621 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333520, d335621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333520, d335621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34749 q selected
  have h8 (q : Pattern) (selected : d333479 q = 0) : d335580 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333479, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34749 q selected
    | true =>
      simp only [d333479, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d333521 q = 0) : d335622 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333521, d335622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333521, d335622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333480 q = 0) : d335581 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333480, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d333480, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d333522 q = 0) : d335623 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333522, d335623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d333522, d335623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d333523 q = 0) : d335624 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333523, d335624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d333523, d335624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d333669 q = 0) : d335745 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d333669, d335745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333669, d335745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d333524 q = 0) : d335625 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d333524, d335625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d333524, d335625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d334146 q = 0) : d336114 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334146, d336114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d334146, d336114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro34873 (p : Pattern) (selected : d334155 p = 0) : d336123 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334138 q = 0) : d336106 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334138, d336106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34869 q selected
    | true =>
      simp only [d334138, d336106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34870 q selected
  have h2 (q : Pattern) (selected : d334139 q = 0) : d336107 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334139, d336107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334139, d336107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334140 q = 0) : d336108 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334140, d336108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334140, d336108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334142 q = 0) : d336110 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334142, d336110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34870 q selected
    | true =>
      simp only [d334142, d336110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34871 q selected
  have h5 (q : Pattern) (selected : d334143 q = 0) : d336111 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334143, d336111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334143, d336111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334144 q = 0) : d336112 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334144, d336112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334144, d336112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334145 q = 0) : d336113 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334145, d336113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334145, d336113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334147 q = 0) : d336115 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334147, d336115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34870 q selected
    | true =>
      simp only [d334147, d336115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34872 q selected
  have h9 (q : Pattern) (selected : d334148 q = 0) : d336116 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334148, d336116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334148, d336116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334149 q = 0) : d336117 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334149, d336117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334149, d336117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d334150 q = 0) : d336118 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334150, d336118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34872 q selected
    | true =>
      simp only [d334150, d336118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34757 q selected
  have h12 (q : Pattern) (selected : d334151 q = 0) : d336119 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334151, d336119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334151, d336119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d334152 q = 0) : d336120 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334152, d336120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334152, d336120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d334153 q = 0) : d336121 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334153, d336121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d334153, d336121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d334154 q = 0) : d336122 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334154, d336122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334154, d336122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d334155 q = 0) : d336123 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334155, d336123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d334155, d336123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro34874 (p : Pattern) (selected : d334160 p = 0) : d336128 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334147 q = 0) : d336115 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334147, d336115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34870 q selected
    | true =>
      simp only [d334147, d336115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34872 q selected
  have h2 (q : Pattern) (selected : d334148 q = 0) : d336116 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334148, d336116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334148, d336116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334149 q = 0) : d336117 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334149, d336117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334149, d336117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334150 q = 0) : d336118 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334150, d336118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34872 q selected
    | true =>
      simp only [d334150, d336118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34757 q selected
  have h5 (q : Pattern) (selected : d334151 q = 0) : d336119 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334151, d336119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334151, d336119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334152 q = 0) : d336120 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334152, d336120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334152, d336120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334153 q = 0) : d336121 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334153, d336121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334153, d336121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334158 q = 0) : d336126 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334158, d336126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334158, d336126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334159 q = 0) : d336127 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334159, d336127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334159, d336127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334160 q = 0) : d336128 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334160, d336128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334160, d336128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro34875 (p : Pattern) (selected : d334166 p = 0) : d336134 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334156 q = 0) : d336124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334156, d336124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34873 q selected
    | true =>
      simp only [d334156, d336124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334157 q = 0) : d336125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334157, d336125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334157, d336125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334161 q = 0) : d336129 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334161, d336129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34874 q selected
    | true =>
      simp only [d334161, d336129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334162 q = 0) : d336130 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334162, d336130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334162, d336130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334163 q = 0) : d336131 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334163, d336131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334163, d336131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334164 q = 0) : d336132 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334164, d336132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334164, d336132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334165 q = 0) : d336133 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334165, d336133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334165, d336133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334166 q = 0) : d336134 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334166, d336134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334166, d336134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro34876 (p : Pattern) (selected : d334168 p = 0) : d336136 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334150 q = 0) : d336118 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334150, d336118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34872 q selected
    | true =>
      simp only [d334150, d336118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34757 q selected
  have h2 (q : Pattern) (selected : d334151 q = 0) : d336119 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334151, d336119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334151, d336119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334152 q = 0) : d336120 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334152, d336120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334152, d336120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334158 q = 0) : d336126 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334158, d336126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334158, d336126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334167 q = 0) : d336135 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334167, d336135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334167, d336135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334168 q = 0) : d336136 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334168, d336136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334168, d336136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34877 (p : Pattern) (selected : d334174 p = 0) : d336142 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334161 q = 0) : d336129 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334161, d336129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34874 q selected
    | true =>
      simp only [d334161, d336129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334162 q = 0) : d336130 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334162, d336130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334162, d336130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334169 q = 0) : d336137 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334169, d336137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34876 q selected
    | true =>
      simp only [d334169, d336137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334170 q = 0) : d336138 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334170, d336138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334170, d336138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334171 q = 0) : d336139 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334171, d336139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334171, d336139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334172 q = 0) : d336140 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334172, d336140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334172, d336140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334173 q = 0) : d336141 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334173, d336141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334173, d336141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334174 q = 0) : d336142 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334174, d336142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334174, d336142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro34878 (p : Pattern) (selected : d334186 p = 0) : d336105 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334176 q = 0) : d335881 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334176, d335881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334176, d335881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34846 q selected
  have h2 (q : Pattern) (selected : d334026 q = 0) : d335808 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334026, d335808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34846 q selected
    | true =>
      simp only [d334026, d335808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334177 q = 0) : d335882 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334177, d335882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334177, d335882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334027 q = 0) : d335809 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334027, d335809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334027, d335809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334178 q = 0) : d335883 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334178, d335883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334178, d335883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334179 q = 0) : d335884 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334179, d335884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334179, d335884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334180 q = 0) : d335885 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334180, d335885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334180, d335885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34847 q selected
  have h8 (q : Pattern) (selected : d334031 q = 0) : d335813 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334031, d335813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34847 q selected
    | true =>
      simp only [d334031, d335813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334181 q = 0) : d335886 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334181, d335886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334181, d335886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334032 q = 0) : d335814 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334032, d335814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d334032, d335814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d334182 q = 0) : d335887 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334182, d335887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334182, d335887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d334183 q = 0) : d335888 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334183, d335888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d334183, d335888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d334184 q = 0) : d335889 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334184, d335889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334184, d335889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d333684 q = 0) : d335621 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333684, d335621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333684, d335621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34770 q selected
  have h15 (q : Pattern) (selected : d333609 q = 0) : d335580 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333609, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34770 q selected
    | true =>
      simp only [d333609, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d333685 q = 0) : d335622 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333685, d335622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d333685, d335622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d333610 q = 0) : d335581 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333610, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d333610, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d333686 q = 0) : d335623 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333686, d335623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d333686, d335623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d333687 q = 0) : d335624 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333687, d335624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d333687, d335624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d334185 q = 0) : d336104 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334185, d336104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334185, d336104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d334186 q = 0) : d336105 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334186, d336105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d334186, d336105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro34879 (p : Pattern) (selected : d334187 p = 0) : d336114 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333875 q = 0) : d335741 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333875, d335741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333875, d335741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34800 q selected
  have h2 (q : Pattern) (selected : d333782 q = 0) : d335687 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333782, d335687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34800 q selected
    | true =>
      simp only [d333782, d335687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333876 q = 0) : d335742 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333876, d335742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333876, d335742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333783 q = 0) : d335688 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333783, d335688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333783, d335688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333877 q = 0) : d335743 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333877, d335743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333877, d335743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333878 q = 0) : d335744 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333878, d335744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333878, d335744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333684 q = 0) : d335621 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333684, d335621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333684, d335621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34770 q selected
  have h8 (q : Pattern) (selected : d333609 q = 0) : d335580 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333609, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34770 q selected
    | true =>
      simp only [d333609, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d333685 q = 0) : d335622 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333685, d335622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333685, d335622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333610 q = 0) : d335581 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333610, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d333610, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d333686 q = 0) : d335623 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333686, d335623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d333686, d335623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d333687 q = 0) : d335624 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333687, d335624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d333687, d335624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d333879 q = 0) : d335745 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d333879, d335745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333879, d335745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d333688 q = 0) : d335625 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d333688, d335625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d333688, d335625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d334187 q = 0) : d336114 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334187, d336114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d334187, d336114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro34880 (p : Pattern) (selected : d334197 p = 0) : d336128 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334188 q = 0) : d336115 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334188, d336115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34878 q selected
    | true =>
      simp only [d334188, d336115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34879 q selected
  have h2 (q : Pattern) (selected : d334189 q = 0) : d336116 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334189, d336116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334189, d336116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334190 q = 0) : d336117 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334190, d336117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334190, d336117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334191 q = 0) : d336118 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334191, d336118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34879 q selected
    | true =>
      simp only [d334191, d336118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34785 q selected
  have h5 (q : Pattern) (selected : d334192 q = 0) : d336119 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334192, d336119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334192, d336119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334193 q = 0) : d336120 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334193, d336120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334193, d336120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334194 q = 0) : d336121 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334194, d336121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334194, d336121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334195 q = 0) : d336126 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334195, d336126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334195, d336126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334196 q = 0) : d336127 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334196, d336127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334196, d336127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334197 q = 0) : d336128 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334197, d336128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334197, d336128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro34881 (p : Pattern) (selected : d334201 p = 0) : d336136 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334191 q = 0) : d336118 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334191, d336118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34879 q selected
    | true =>
      simp only [d334191, d336118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34785 q selected
  have h2 (q : Pattern) (selected : d334192 q = 0) : d336119 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334192, d336119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334192, d336119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334193 q = 0) : d336120 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334193, d336120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334193, d336120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334195 q = 0) : d336126 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334195, d336126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334195, d336126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334200 q = 0) : d336135 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334200, d336135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334200, d336135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334201 q = 0) : d336136 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334201, d336136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334201, d336136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34882 (p : Pattern) (selected : d334207 p = 0) : d336142 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334198 q = 0) : d336129 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334198, d336129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34880 q selected
    | true =>
      simp only [d334198, d336129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334199 q = 0) : d336130 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334199, d336130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334199, d336130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334202 q = 0) : d336137 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334202, d336137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34881 q selected
    | true =>
      simp only [d334202, d336137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334203 q = 0) : d336138 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334203, d336138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334203, d336138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334204 q = 0) : d336139 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334204, d336139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334204, d336139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334205 q = 0) : d336140 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334205, d336140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334205, d336140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334206 q = 0) : d336141 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334206, d336141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334206, d336141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334207 q = 0) : d336142 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334207, d336142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334207, d336142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro34883 (p : Pattern) (selected : d334211 p = 0) : d336147 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334202 q = 0) : d336137 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334202, d336137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34881 q selected
    | true =>
      simp only [d334202, d336137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334203 q = 0) : d336138 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334203, d336138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334203, d336138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334208 q = 0) : d336144 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334208, d336144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334208, d336144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334209 q = 0) : d336145 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334209, d336145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334209, d336145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334210 q = 0) : d336146 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334210, d336146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334210, d336146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334211 q = 0) : d336147 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334211, d336147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334211, d336147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34884 (p : Pattern) (selected : d334217 p = 0) : d336153 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334161 q = 0) : d336129 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334161, d336129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34874 q selected
    | true =>
      simp only [d334161, d336129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334162 q = 0) : d336130 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334162, d336130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334162, d336130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334214 q = 0) : d336150 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334214, d336150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334214, d336150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334215 q = 0) : d336151 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334215, d336151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334215, d336151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334216 q = 0) : d336152 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334216, d336152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334216, d336152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334217 q = 0) : d336153 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334217, d336153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334217, d336153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34885 (p : Pattern) (selected : d334223 p = 0) : d336159 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334175 q = 0) : d336143 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334175, d336143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34875 q selected
    | true =>
      simp only [d334175, d336143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34877 q selected
  have h2 (q : Pattern) (selected : d334212 q = 0) : d336148 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334212, d336148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34882 q selected
    | true =>
      simp only [d334212, d336148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34883 q selected
  have h3 (q : Pattern) (selected : d334213 q = 0) : d336149 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334213, d336149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334213, d336149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334218 q = 0) : d336154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334218, d336154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34884 q selected
    | true =>
      simp only [d334218, d336154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334219 q = 0) : d336155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334219, d336155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334219, d336155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334220 q = 0) : d336156 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334220, d336156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334220, d336156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334221 q = 0) : d336157 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334221, d336157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334221, d336157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334222 q = 0) : d336158 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334222, d336158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334222, d336158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d334223 q = 0) : d336159 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d334223, d336159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334223, d336159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro34886 (p : Pattern) (selected : d334228 p = 0) : d336147 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334169 q = 0) : d336137 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334169, d336137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34876 q selected
    | true =>
      simp only [d334169, d336137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334170 q = 0) : d336138 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334170, d336138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334170, d336138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334225 q = 0) : d336144 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334225, d336144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334225, d336144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334226 q = 0) : d336145 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334226, d336145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334226, d336145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334227 q = 0) : d336146 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334227, d336146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334227, d336146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334228 q = 0) : d336147 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334228, d336147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334228, d336147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34887 (p : Pattern) (selected : d334234 p = 0) : d336166 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334229 q = 0) : d336161 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334229, d336161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34886 q selected
    | true =>
      simp only [d334229, d336161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334230 q = 0) : d336162 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334230, d336162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334230, d336162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334231 q = 0) : d336163 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334231, d336163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334231, d336163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334232 q = 0) : d336164 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334232, d336164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334232, d336164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334233 q = 0) : d336165 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334233, d336165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334233, d336165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334234 q = 0) : d336166 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d334234, d336166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334234, d336166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro34888 (p : Pattern) (selected : d334240 p = 0) : d336172 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333957 q = 0) : d335970 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333957, d335970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333957, d335970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34832 q selected
  have h2 (q : Pattern) (selected : d333958 q = 0) : d335971 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333958, d335971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333958, d335971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333967 q = 0) : d335980 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d333967, d335980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34832 q selected
    | true =>
      simp only [d333967, d335980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34835 q selected
  have h4 (q : Pattern) (selected : d333968 q = 0) : d335981 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d333968, d335981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333968, d335981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333969 q = 0) : d335982 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d333969, d335982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333969, d335982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334099 q = 0) : d336067 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d334099, d336067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34855 q selected
    | true =>
      simp only [d334099, d336067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34864 q selected
  have h7 (q : Pattern) (selected : d334112 q = 0) : d336080 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d334112, d336080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34865 q selected
    | true =>
      simp only [d334112, d336080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34866 q selected
  have h8 (q : Pattern) (selected : d334113 q = 0) : d336081 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d334113, d336081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334113, d336081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d334114 q = 0) : d336082 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d334114, d336082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d334114, d336082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d334115 q = 0) : d336083 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d334115, d336083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334115, d336083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d334119 q = 0) : d336087 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d334119, d336087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334119, d336087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34867 q selected
  have h12 (q : Pattern) (selected : d334121 q = 0) : d336089 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d334121, d336089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334121, d336089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34868 q selected
  have h13 (q : Pattern) (selected : d334122 q = 0) : d336090 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d334122, d336090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d334122, d336090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d334123 q = 0) : d336091 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d334123, d336091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d334123, d336091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d334124 q = 0) : d336092 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d334124, d336092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d334124, d336092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d334125 q = 0) : d336093 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d334125, d336093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d334125, d336093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d334224 q = 0) : d336160 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d334224, d336160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334224, d336160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34885 q selected
  have h18 (q : Pattern) (selected : d334235 q = 0) : d336167 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d334235, d336167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334235, d336167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34887 q selected
  have h19 (q : Pattern) (selected : d334236 q = 0) : d336168 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d334236, d336168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d334236, d336168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d334237 q = 0) : d336169 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d334237, d336169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d334237, d336169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d334238 q = 0) : d336170 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d334238, d336170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d334238, d336170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d334239 q = 0) : d336171 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d334239, d336171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d334239, d336171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d334240 q = 0) : d336172 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d334240, d336172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d334240, d336172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro34889 (p : Pattern) (selected : d334246 p = 0) : d336178 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334241 q = 0) : d336173 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d334241, d336173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334241, d336173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34888 q selected
  have h2 (q : Pattern) (selected : d334242 q = 0) : d336174 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d334242, d336174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334242, d336174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334243 q = 0) : d336175 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d334243, d336175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334243, d336175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334244 q = 0) : d336176 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d334244, d336176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334244, d336176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334245 q = 0) : d336177 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d334245, d336177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334245, d336177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334246 q = 0) : d336178 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d334246, d336178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334246, d336178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro34890 (p : Pattern) (selected : d334251 p = 0) : d336183 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333582 q = 0) : d335683 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333582, d335683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro204 q selected
    | true =>
      simp only [d333582, d335683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334249 q = 0) : d336181 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334249, d336181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334249, d336181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334250 q = 0) : d336182 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334250, d336182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334250, d336182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333475 q = 0) : d335576 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333475, d335576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
    | true =>
      simp only [d333475, d335576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333476 q = 0) : d335577 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d333476, d335577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333476, d335577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333477 q = 0) : d335578 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d333477, d335578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333477, d335578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334251 q = 0) : d336183 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d334251, d336183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334251, d336183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro34891 (p : Pattern) (selected : d334257 p = 0) : d336189 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333994 q = 0) : d336007 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333994, d336007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34840 q selected
    | true =>
      simp only [d333994, d336007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333995 q = 0) : d336008 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333995, d336008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333995, d336008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333996 q = 0) : d336009 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333996, d336009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333996, d336009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333997 q = 0) : d336010 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333997, d336010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333997, d336010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333999 q = 0) : d336012 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333999, d336012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34841 q selected
    | true =>
      simp only [d333999, d336012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334000 q = 0) : d336013 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334000, d336013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334000, d336013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334001 q = 0) : d336014 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334001, d336014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334001, d336014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334002 q = 0) : d336015 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334002, d336015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334002, d336015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334003 q = 0) : d336016 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334003, d336016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334003, d336016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334252 q = 0) : d336184 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334252, d336184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34890 q selected
    | true =>
      simp only [d334252, d336184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d334253 q = 0) : d336185 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334253, d336185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d334253, d336185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d334254 q = 0) : d336186 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334254, d336186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334254, d336186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d334255 q = 0) : d336187 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334255, d336187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d334255, d336187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d334256 q = 0) : d336188 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334256, d336188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334256, d336188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d334257 q = 0) : d336189 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334257, d336189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334257, d336189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro34892 (p : Pattern) (selected : d334260 p = 0) : d336192 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333751 q = 0) : d335808 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333751, d335808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34795 q selected
    | true =>
      simp only [d333751, d335808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333752 q = 0) : d335809 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333752, d335809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333752, d335809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333753 q = 0) : d335810 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333753, d335810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333753, d335810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333754 q = 0) : d335811 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333754, d335811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333754, d335811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333586 q = 0) : d335687 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333586, d335687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34766 q selected
    | true =>
      simp only [d333586, d335687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333587 q = 0) : d335688 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333587, d335688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333587, d335688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333588 q = 0) : d335689 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333588, d335689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333588, d335689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333589 q = 0) : d335690 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333589, d335690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333589, d335690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334258 q = 0) : d336190 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334258, d336190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334258, d336190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334252 q = 0) : d336184 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334252, d336184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34890 q selected
    | true =>
      simp only [d334252, d336184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d334253 q = 0) : d336185 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334253, d336185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d334253, d336185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d334254 q = 0) : d336186 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334254, d336186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334254, d336186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d334255 q = 0) : d336187 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334255, d336187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d334255, d336187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d334259 q = 0) : d336191 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334259, d336191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d334259, d336191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d334260 q = 0) : d336192 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334260, d336192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334260, d336192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro34893 (p : Pattern) (selected : d334265 p = 0) : d336197 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333586 q = 0) : d335687 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333586, d335687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34766 q selected
    | true =>
      simp only [d333586, d335687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333587 q = 0) : d335688 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333587, d335688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333587, d335688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333588 q = 0) : d335689 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333588, d335689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333588, d335689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333589 q = 0) : d335690 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333589, d335690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333589, d335690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334264 q = 0) : d336196 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334264, d336196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334264, d336196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333479 q = 0) : d335580 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333479, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34749 q selected
    | true =>
      simp only [d333479, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333480 q = 0) : d335581 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333480, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333480, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d333481 q = 0) : d335582 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333481, d335582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333481, d335582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d333482 q = 0) : d335583 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333482, d335583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d333482, d335583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d333483 q = 0) : d335584 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d333483, d335584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d333483, d335584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d334265 q = 0) : d336197 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334265, d336197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334265, d336197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro34894 (p : Pattern) (selected : d334272 p = 0) : d336204 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334261 q = 0) : d336193 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334261, d336193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34891 q selected
    | true =>
      simp only [d334261, d336193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34892 q selected
  have h2 (q : Pattern) (selected : d334262 q = 0) : d336194 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334262, d336194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334262, d336194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334263 q = 0) : d336195 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334263, d336195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334263, d336195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334266 q = 0) : d336198 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334266, d336198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34892 q selected
    | true =>
      simp only [d334266, d336198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34893 q selected
  have h5 (q : Pattern) (selected : d334267 q = 0) : d336199 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334267, d336199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334267, d336199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334268 q = 0) : d336200 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334268, d336200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334268, d336200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334269 q = 0) : d336201 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334269, d336201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334269, d336201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334270 q = 0) : d336202 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334270, d336202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334270, d336202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334271 q = 0) : d336203 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334271, d336203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334271, d336203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334272 q = 0) : d336204 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334272, d336204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334272, d336204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro34895 (p : Pattern) (selected : d334276 p = 0) : d336208 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334266 q = 0) : d336198 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334266, d336198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34892 q selected
    | true =>
      simp only [d334266, d336198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34893 q selected
  have h2 (q : Pattern) (selected : d334267 q = 0) : d336199 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334267, d336199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334267, d336199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334268 q = 0) : d336200 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334268, d336200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334268, d336200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334270 q = 0) : d336202 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334270, d336202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334270, d336202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334275 q = 0) : d336207 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334275, d336207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334275, d336207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334276 q = 0) : d336208 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334276, d336208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334276, d336208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34896 (p : Pattern) (selected : d334282 p = 0) : d336214 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334273 q = 0) : d336205 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334273, d336205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34894 q selected
    | true =>
      simp only [d334273, d336205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334274 q = 0) : d336206 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334274, d336206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334274, d336206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334277 q = 0) : d336209 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334277, d336209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34895 q selected
    | true =>
      simp only [d334277, d336209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334278 q = 0) : d336210 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334278, d336210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334278, d336210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334279 q = 0) : d336211 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334279, d336211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334279, d336211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334280 q = 0) : d336212 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334280, d336212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334280, d336212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334281 q = 0) : d336213 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334281, d336213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334281, d336213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334282 q = 0) : d336214 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334282, d336214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334282, d336214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro34897 (p : Pattern) (selected : d334286 p = 0) : d336218 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334277 q = 0) : d336209 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334277, d336209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34895 q selected
    | true =>
      simp only [d334277, d336209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334278 q = 0) : d336210 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334278, d336210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334278, d336210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334283 q = 0) : d336215 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334283, d336215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334283, d336215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334284 q = 0) : d336216 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334284, d336216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334284, d336216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334285 q = 0) : d336217 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334285, d336217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334285, d336217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334286 q = 0) : d336218 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334286, d336218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334286, d336218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro34898 (p : Pattern) (selected : d334292 p = 0) : d336224 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334287 q = 0) : d336219 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334287, d336219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34896 q selected
    | true =>
      simp only [d334287, d336219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34897 q selected
  have h2 (q : Pattern) (selected : d334288 q = 0) : d336220 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334288, d336220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334288, d336220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334289 q = 0) : d336221 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334289, d336221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334289, d336221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334290 q = 0) : d336222 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334290, d336222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334290, d336222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334291 q = 0) : d336223 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334291, d336223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334291, d336223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334292 q = 0) : d336224 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d334292, d336224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334292, d336224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro34899 (p : Pattern) (selected : d334295 p = 0) : d336227 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334273 q = 0) : d336205 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334273, d336205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34894 q selected
    | true =>
      simp only [d334273, d336205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334274 q = 0) : d336206 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334274, d336206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334274, d336206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334277 q = 0) : d336209 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334277, d336209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34895 q selected
    | true =>
      simp only [d334277, d336209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334278 q = 0) : d336210 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334278, d336210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334278, d336210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334279 q = 0) : d336211 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334279, d336211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334279, d336211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334280 q = 0) : d336212 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334280, d336212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334280, d336212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334281 q = 0) : d336213 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334281, d336213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334281, d336213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334295 q = 0) : d336227 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334295, d336227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334295, d336227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro34900 (p : Pattern) (selected : d334296 p = 0) : d336228 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334277 q = 0) : d336209 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334277, d336209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34895 q selected
    | true =>
      simp only [d334277, d336209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334278 q = 0) : d336210 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334278, d336210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334278, d336210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334283 q = 0) : d336215 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334283, d336215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334283, d336215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334284 q = 0) : d336216 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334284, d336216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334284, d336216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334285 q = 0) : d336217 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334285, d336217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334285, d336217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334296 q = 0) : d336228 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334296, d336228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334296, d336228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34901 (p : Pattern) (selected : d334302 p = 0) : d336234 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334287 q = 0) : d336219 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334287, d336219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34896 q selected
    | true =>
      simp only [d334287, d336219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34897 q selected
  have h2 (q : Pattern) (selected : d334288 q = 0) : d336220 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334288, d336220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334288, d336220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334289 q = 0) : d336221 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334289, d336221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334289, d336221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334290 q = 0) : d336222 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334290, d336222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334290, d336222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334291 q = 0) : d336223 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334291, d336223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334291, d336223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334297 q = 0) : d336229 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334297, d336229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34899 q selected
    | true =>
      simp only [d334297, d336229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34900 q selected
  have h7 (q : Pattern) (selected : d334298 q = 0) : d336230 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334298, d336230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334298, d336230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334299 q = 0) : d336231 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334299, d336231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334299, d336231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334300 q = 0) : d336232 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334300, d336232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334300, d336232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334301 q = 0) : d336233 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334301, d336233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334301, d336233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d334302 q = 0) : d336234 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d334302, d336234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334302, d336234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro34902 (p : Pattern) (selected : d334307 p = 0) : d336239 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334273 q = 0) : d336205 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334273, d336205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34894 q selected
    | true =>
      simp only [d334273, d336205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334274 q = 0) : d336206 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334274, d336206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334274, d336206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334277 q = 0) : d336209 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334277, d336209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34895 q selected
    | true =>
      simp only [d334277, d336209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334278 q = 0) : d336210 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334278, d336210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334278, d336210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334279 q = 0) : d336211 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334279, d336211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334279, d336211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334280 q = 0) : d336212 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334280, d336212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334280, d336212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334306 q = 0) : d336238 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334306, d336238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334306, d336238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334307 q = 0) : d336239 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334307, d336239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334307, d336239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro34903 (p : Pattern) (selected : d334309 p = 0) : d336241 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334277 q = 0) : d336209 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334277, d336209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34895 q selected
    | true =>
      simp only [d334277, d336209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334278 q = 0) : d336210 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334278, d336210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334278, d336210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334283 q = 0) : d336215 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334283, d336215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334283, d336215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334284 q = 0) : d336216 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334284, d336216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334284, d336216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334308 q = 0) : d336240 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334308, d336240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334308, d336240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334309 q = 0) : d336241 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334309, d336241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334309, d336241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro34904 (p : Pattern) (selected : d334316 p = 0) : d336248 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334273 q = 0) : d336205 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334273, d336205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34894 q selected
    | true =>
      simp only [d334273, d336205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334274 q = 0) : d336206 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334274, d336206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334274, d336206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334277 q = 0) : d336209 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334277, d336209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34895 q selected
    | true =>
      simp only [d334277, d336209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334278 q = 0) : d336210 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334278, d336210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334278, d336210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334279 q = 0) : d336211 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334279, d336211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334279, d336211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334314 q = 0) : d336246 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334314, d336246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334314, d336246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334315 q = 0) : d336247 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334315, d336247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334315, d336247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334316 q = 0) : d336248 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334316, d336248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334316, d336248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro34905 (p : Pattern) (selected : d334319 p = 0) : d336251 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334277 q = 0) : d336209 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334277, d336209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34895 q selected
    | true =>
      simp only [d334277, d336209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334278 q = 0) : d336210 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334278, d336210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334278, d336210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334283 q = 0) : d336215 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334283, d336215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334283, d336215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334317 q = 0) : d336249 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334317, d336249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334317, d336249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334318 q = 0) : d336250 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334318, d336250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334318, d336250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334319 q = 0) : d336251 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334319, d336251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334319, d336251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro34906 (p : Pattern) (selected : d334325 p = 0) : d336257 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333988 q = 0) : d336001 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333988, d336001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23520 q selected
    | true =>
      simp only [d333988, d336001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334323 q = 0) : d336255 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334323, d336255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334323, d336255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334324 q = 0) : d336256 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334324, d336256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334324, d336256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334325 q = 0) : d336257 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d334325, d336257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334325, d336257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h4 p selected
theorem eqIntro34907 (p : Pattern) (selected : d334330 p = 0) : d336262 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333987 q = 0) : d336000 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333987, d336000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23519 q selected
    | true =>
      simp only [d333987, d336000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333988 q = 0) : d336001 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333988, d336001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23520 q selected
    | true =>
      simp only [d333988, d336001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333989 q = 0) : d336002 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d333989, d336002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333989, d336002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333990 q = 0) : d336003 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d333990, d336003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333990, d336003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334330 q = 0) : d336262 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d334330, d336262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334330, d336262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro34908 (p : Pattern) (selected : d334336 p = 0) : d336268 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334326 q = 0) : d336258 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334326, d336258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34906 q selected
    | true =>
      simp only [d334326, d336258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334327 q = 0) : d336259 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334327, d336259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334327, d336259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334328 q = 0) : d336260 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334328, d336260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334328, d336260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334329 q = 0) : d336261 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334329, d336261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334329, d336261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334331 q = 0) : d336263 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334331, d336263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34907 q selected
    | true =>
      simp only [d334331, d336263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334332 q = 0) : d336264 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334332, d336264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334332, d336264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334333 q = 0) : d336265 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334333, d336265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334333, d336265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334334 q = 0) : d336266 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334334, d336266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334334, d336266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334335 q = 0) : d336267 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334335, d336267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334335, d336267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334336 q = 0) : d336268 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334336, d336268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334336, d336268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro34909 (p : Pattern) (selected : d334340 p = 0) : d336272 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334252 q = 0) : d336184 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334252, d336184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34890 q selected
    | true =>
      simp only [d334252, d336184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334253 q = 0) : d336185 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334253, d336185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334253, d336185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334254 q = 0) : d336186 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334254, d336186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334254, d336186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334255 q = 0) : d336187 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334255, d336187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334255, d336187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334256 q = 0) : d336188 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334256, d336188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334256, d336188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334259 q = 0) : d336191 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334259, d336191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334259, d336191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334340 q = 0) : d336272 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334340, d336272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334340, d336272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro34910 (p : Pattern) (selected : d334346 p = 0) : d336278 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334337 q = 0) : d336269 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334337, d336269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34908 q selected
    | true =>
      simp only [d334337, d336269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34891 q selected
  have h2 (q : Pattern) (selected : d334338 q = 0) : d336270 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334338, d336270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334338, d336270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334339 q = 0) : d336271 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334339, d336271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334339, d336271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334341 q = 0) : d336273 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334341, d336273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34891 q selected
    | true =>
      simp only [d334341, d336273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34909 q selected
  have h5 (q : Pattern) (selected : d334342 q = 0) : d336274 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334342, d336274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334342, d336274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334343 q = 0) : d336275 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334343, d336275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334343, d336275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334344 q = 0) : d336276 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334344, d336276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334344, d336276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334261 q = 0) : d336193 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334261, d336193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34891 q selected
    | true =>
      simp only [d334261, d336193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34892 q selected
  have h9 (q : Pattern) (selected : d334262 q = 0) : d336194 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334262, d336194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334262, d336194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334263 q = 0) : d336195 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334263, d336195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334263, d336195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d334266 q = 0) : d336198 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334266, d336198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34892 q selected
    | true =>
      simp only [d334266, d336198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34893 q selected
  have h12 (q : Pattern) (selected : d334267 q = 0) : d336199 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334267, d336199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334267, d336199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d334268 q = 0) : d336200 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334268, d336200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334268, d336200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d334269 q = 0) : d336201 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334269, d336201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d334269, d336201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d334345 q = 0) : d336277 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334345, d336277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334345, d336277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d334346 q = 0) : d336278 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334346, d336278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d334346, d336278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro34911 (p : Pattern) (selected : d334352 p = 0) : d336284 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334347 q = 0) : d336279 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334347, d336279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34910 q selected
    | true =>
      simp only [d334347, d336279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334348 q = 0) : d336280 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334348, d336280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334348, d336280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334273 q = 0) : d336205 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334273, d336205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34894 q selected
    | true =>
      simp only [d334273, d336205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334274 q = 0) : d336206 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334274, d336206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334274, d336206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334349 q = 0) : d336281 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334349, d336281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334349, d336281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334350 q = 0) : d336282 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334350, d336282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334350, d336282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334351 q = 0) : d336283 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334351, d336283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334351, d336283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334352 q = 0) : d336284 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334352, d336284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334352, d336284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro34912 (p : Pattern) (selected : d334360 p = 0) : d336006 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334354 q = 0) : d336000 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334354, d336000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23581 q selected
    | true =>
      simp only [d334354, d336000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334355 q = 0) : d336001 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334355, d336001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23582 q selected
    | true =>
      simp only [d334355, d336001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334356 q = 0) : d336002 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334356, d336002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334356, d336002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334357 q = 0) : d336003 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334357, d336003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334357, d336003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333778 q = 0) : d335683 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333778, d335683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro239 q selected
    | true =>
      simp only [d333778, d335683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334358 q = 0) : d336004 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334358, d336004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334358, d336004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334359 q = 0) : d336005 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334359, d336005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334359, d336005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334360 q = 0) : d336006 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d334360, d336006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334360, d336006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro34913 (p : Pattern) (selected : d334365 p = 0) : d336011 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334022 q = 0) : d335804 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334022, d335804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23527 q selected
    | true =>
      simp only [d334022, d335804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333778 q = 0) : d335683 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333778, d335683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro239 q selected
    | true =>
      simp only [d333778, d335683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334023 q = 0) : d335805 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334023, d335805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334023, d335805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334024 q = 0) : d335806 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334024, d335806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334024, d335806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334365 q = 0) : d336011 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d334365, d336011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334365, d336011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro34914 (p : Pattern) (selected : d334373 p = 0) : d336183 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333778 q = 0) : d335683 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333778, d335683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro239 q selected
    | true =>
      simp only [d333778, d335683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334371 q = 0) : d336181 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334371, d336181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334371, d336181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334372 q = 0) : d336182 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334372, d336182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334372, d336182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d333605 q = 0) : d335576 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333605, d335576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
    | true =>
      simp only [d333605, d335576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333606 q = 0) : d335577 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d333606, d335577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d333606, d335577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333607 q = 0) : d335578 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d333607, d335578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333607, d335578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334373 q = 0) : d336183 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d334373, d336183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334373, d336183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro34915 (p : Pattern) (selected : d334379 p = 0) : d336189 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334361 q = 0) : d336007 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334361, d336007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34912 q selected
    | true =>
      simp only [d334361, d336007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334362 q = 0) : d336008 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334362, d336008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334362, d336008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334363 q = 0) : d336009 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334363, d336009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334363, d336009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334364 q = 0) : d336010 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334364, d336010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334364, d336010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334366 q = 0) : d336012 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334366, d336012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34913 q selected
    | true =>
      simp only [d334366, d336012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334367 q = 0) : d336013 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334367, d336013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334367, d336013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334368 q = 0) : d336014 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334368, d336014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334368, d336014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334369 q = 0) : d336015 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334369, d336015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334369, d336015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334370 q = 0) : d336016 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334370, d336016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334370, d336016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334374 q = 0) : d336184 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334374, d336184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34914 q selected
    | true =>
      simp only [d334374, d336184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d334375 q = 0) : d336185 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334375, d336185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d334375, d336185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d334376 q = 0) : d336186 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334376, d336186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334376, d336186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d334377 q = 0) : d336187 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334377, d336187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d334377, d336187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d334378 q = 0) : d336188 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334378, d336188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334378, d336188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d334379 q = 0) : d336189 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334379, d336189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334379, d336189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro34916 (p : Pattern) (selected : d334382 p = 0) : d336192 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334026 q = 0) : d335808 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334026, d335808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34846 q selected
    | true =>
      simp only [d334026, d335808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334027 q = 0) : d335809 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334027, d335809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334027, d335809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334028 q = 0) : d335810 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334028, d335810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334028, d335810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334029 q = 0) : d335811 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334029, d335811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334029, d335811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333782 q = 0) : d335687 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333782, d335687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34800 q selected
    | true =>
      simp only [d333782, d335687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333783 q = 0) : d335688 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333783, d335688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333783, d335688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333784 q = 0) : d335689 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333784, d335689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333784, d335689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d333785 q = 0) : d335690 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333785, d335690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333785, d335690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334380 q = 0) : d336190 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334380, d336190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334380, d336190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334374 q = 0) : d336184 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334374, d336184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34914 q selected
    | true =>
      simp only [d334374, d336184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d334375 q = 0) : d336185 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334375, d336185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d334375, d336185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d334376 q = 0) : d336186 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334376, d336186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334376, d336186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d334377 q = 0) : d336187 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334377, d336187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d334377, d336187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d334381 q = 0) : d336191 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334381, d336191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d334381, d336191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d334382 q = 0) : d336192 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334382, d336192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334382, d336192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro34917 (p : Pattern) (selected : d334387 p = 0) : d336197 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333782 q = 0) : d335687 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333782, d335687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34800 q selected
    | true =>
      simp only [d333782, d335687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333783 q = 0) : d335688 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333783, d335688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333783, d335688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333784 q = 0) : d335689 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333784, d335689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333784, d335689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333785 q = 0) : d335690 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333785, d335690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333785, d335690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334386 q = 0) : d336196 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334386, d336196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334386, d336196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d333609 q = 0) : d335580 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333609, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34770 q selected
    | true =>
      simp only [d333609, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333610 q = 0) : d335581 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333610, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d333610, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d333611 q = 0) : d335582 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333611, d335582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333611, d335582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d333612 q = 0) : d335583 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333612, d335583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d333612, d335583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d333613 q = 0) : d335584 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d333613, d335584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d333613, d335584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d334387 q = 0) : d336197 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334387, d336197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334387, d336197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro34918 (p : Pattern) (selected : d334394 p = 0) : d336204 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334383 q = 0) : d336193 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334383, d336193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34915 q selected
    | true =>
      simp only [d334383, d336193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34916 q selected
  have h2 (q : Pattern) (selected : d334384 q = 0) : d336194 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334384, d336194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334384, d336194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334385 q = 0) : d336195 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334385, d336195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334385, d336195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334388 q = 0) : d336198 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334388, d336198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34916 q selected
    | true =>
      simp only [d334388, d336198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34917 q selected
  have h5 (q : Pattern) (selected : d334389 q = 0) : d336199 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334389, d336199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334389, d336199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334390 q = 0) : d336200 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334390, d336200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334390, d336200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334391 q = 0) : d336201 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334391, d336201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334391, d336201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334392 q = 0) : d336202 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334392, d336202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334392, d336202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334393 q = 0) : d336203 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334393, d336203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334393, d336203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334394 q = 0) : d336204 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334394, d336204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334394, d336204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro34919 (p : Pattern) (selected : d334398 p = 0) : d336208 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334388 q = 0) : d336198 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334388, d336198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34916 q selected
    | true =>
      simp only [d334388, d336198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34917 q selected
  have h2 (q : Pattern) (selected : d334389 q = 0) : d336199 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334389, d336199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334389, d336199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334390 q = 0) : d336200 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334390, d336200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334390, d336200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334392 q = 0) : d336202 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334392, d336202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334392, d336202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334397 q = 0) : d336207 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334397, d336207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334397, d336207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334398 q = 0) : d336208 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334398, d336208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334398, d336208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34920 (p : Pattern) (selected : d334404 p = 0) : d336214 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334395 q = 0) : d336205 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334395, d336205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34918 q selected
    | true =>
      simp only [d334395, d336205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334396 q = 0) : d336206 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334396, d336206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334396, d336206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334399 q = 0) : d336209 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334399, d336209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34919 q selected
    | true =>
      simp only [d334399, d336209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334400 q = 0) : d336210 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334400, d336210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334400, d336210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334401 q = 0) : d336211 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334401, d336211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334401, d336211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334402 q = 0) : d336212 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334402, d336212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334402, d336212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334403 q = 0) : d336213 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334403, d336213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334403, d336213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334404 q = 0) : d336214 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334404, d336214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334404, d336214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro34921 (p : Pattern) (selected : d334408 p = 0) : d336218 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334399 q = 0) : d336209 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334399, d336209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34919 q selected
    | true =>
      simp only [d334399, d336209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334400 q = 0) : d336210 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334400, d336210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334400, d336210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334405 q = 0) : d336215 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334405, d336215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334405, d336215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334406 q = 0) : d336216 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334406, d336216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334406, d336216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334407 q = 0) : d336217 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334407, d336217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334407, d336217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334408 q = 0) : d336218 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334408, d336218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334408, d336218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro34922 (p : Pattern) (selected : d334411 p = 0) : d336287 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333586 q = 0) : d335687 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333586, d335687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34766 q selected
    | true =>
      simp only [d333586, d335687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d333587 q = 0) : d335688 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333587, d335688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333587, d335688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333588 q = 0) : d335689 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333588, d335689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333588, d335689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333589 q = 0) : d335690 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333589, d335690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333589, d335690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334264 q = 0) : d336196 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334264, d336196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334264, d336196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334411 q = 0) : d336287 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334411, d336287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334411, d336287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34923 (p : Pattern) (selected : d334417 p = 0) : d336293 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334261 q = 0) : d336193 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334261, d336193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34891 q selected
    | true =>
      simp only [d334261, d336193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34892 q selected
  have h2 (q : Pattern) (selected : d334262 q = 0) : d336194 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334262, d336194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334262, d336194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334263 q = 0) : d336195 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334263, d336195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334263, d336195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334266 q = 0) : d336198 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334266, d336198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34892 q selected
    | true =>
      simp only [d334266, d336198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34893 q selected
  have h5 (q : Pattern) (selected : d334267 q = 0) : d336199 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334267, d336199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334267, d336199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334268 q = 0) : d336200 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334268, d336200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334268, d336200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334269 q = 0) : d336201 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334269, d336201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334269, d336201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334412 q = 0) : d336288 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334412, d336288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34892 q selected
    | true =>
      simp only [d334412, d336288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34922 q selected
  have h9 (q : Pattern) (selected : d334413 q = 0) : d336289 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334413, d336289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334413, d336289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334414 q = 0) : d336290 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334414, d336290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334414, d336290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d334415 q = 0) : d336291 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334415, d336291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d334415, d336291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d334416 q = 0) : d336292 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334416, d336292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334416, d336292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d334417 q = 0) : d336293 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334417, d336293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d334417, d336293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro34924 (p : Pattern) (selected : d334423 p = 0) : d336299 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334418 q = 0) : d336294 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334418, d336294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34923 q selected
    | true =>
      simp only [d334418, d336294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334419 q = 0) : d336295 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334419, d336295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334419, d336295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334420 q = 0) : d336296 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334420, d336296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334420, d336296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334421 q = 0) : d336297 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334421, d336297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334421, d336297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334422 q = 0) : d336298 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334422, d336298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334422, d336298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334423 q = 0) : d336299 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334423, d336299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334423, d336299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro34925 (p : Pattern) (selected : d334429 p = 0) : d336305 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334310 q = 0) : d336242 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334310, d336242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34902 q selected
    | true =>
      simp only [d334310, d336242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34903 q selected
  have h2 (q : Pattern) (selected : d334311 q = 0) : d336243 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334311, d336243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334311, d336243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334312 q = 0) : d336244 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334312, d336244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334312, d336244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334313 q = 0) : d336245 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334313, d336245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334313, d336245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334320 q = 0) : d336252 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334320, d336252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34904 q selected
    | true =>
      simp only [d334320, d336252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34905 q selected
  have h6 (q : Pattern) (selected : d334321 q = 0) : d336253 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334321, d336253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334321, d336253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334322 q = 0) : d336254 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334322, d336254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334322, d336254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334353 q = 0) : d336285 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334353, d336285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34911 q selected
    | true =>
      simp only [d334353, d336285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34896 q selected
  have h9 (q : Pattern) (selected : d334409 q = 0) : d336219 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334409, d336219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34920 q selected
    | true =>
      simp only [d334409, d336219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34921 q selected
  have h10 (q : Pattern) (selected : d334410 q = 0) : d336286 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334410, d336286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d334410, d336286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d334424 q = 0) : d336300 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334424, d336300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34924 q selected
    | true =>
      simp only [d334424, d336300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d334425 q = 0) : d336301 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334425, d336301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d334425, d336301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d334426 q = 0) : d336302 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334426, d336302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d334426, d336302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d334427 q = 0) : d336303 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334427, d336303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334427, d336303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d334428 q = 0) : d336304 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334428, d336304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334428, d336304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d334429 q = 0) : d336305 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d334429, d336305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334429, d336305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro34926 (p : Pattern) (selected : d334430 p = 0) : d336306 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334273 q = 0) : d336205 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334273, d336205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34894 q selected
    | true =>
      simp only [d334273, d336205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334274 q = 0) : d336206 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334274, d336206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334274, d336206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334277 q = 0) : d336209 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334277, d336209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34895 q selected
    | true =>
      simp only [d334277, d336209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334278 q = 0) : d336210 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334278, d336210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334278, d336210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334279 q = 0) : d336211 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334279, d336211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334279, d336211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334280 q = 0) : d336212 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334280, d336212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334280, d336212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334306 q = 0) : d336238 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334306, d336238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334306, d336238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334430 q = 0) : d336306 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334430, d336306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334430, d336306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro34927 (p : Pattern) (selected : d334431 p = 0) : d336307 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334277 q = 0) : d336209 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334277, d336209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34895 q selected
    | true =>
      simp only [d334277, d336209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334278 q = 0) : d336210 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334278, d336210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334278, d336210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334283 q = 0) : d336215 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334283, d336215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334283, d336215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334284 q = 0) : d336216 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334284, d336216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334284, d336216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334308 q = 0) : d336240 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334308, d336240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334308, d336240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334431 q = 0) : d336307 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334431, d336307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334431, d336307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34928 (p : Pattern) (selected : d334436 p = 0) : d336312 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334273 q = 0) : d336205 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334273, d336205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34894 q selected
    | true =>
      simp only [d334273, d336205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334274 q = 0) : d336206 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334274, d336206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334274, d336206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334277 q = 0) : d336209 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334277, d336209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34895 q selected
    | true =>
      simp only [d334277, d336209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334278 q = 0) : d336210 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334278, d336210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334278, d336210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334279 q = 0) : d336211 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334279, d336211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334279, d336211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334314 q = 0) : d336246 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334314, d336246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334314, d336246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334315 q = 0) : d336247 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334315, d336247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334315, d336247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334436 q = 0) : d336312 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334436, d336312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334436, d336312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro34929 (p : Pattern) (selected : d334437 p = 0) : d336313 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334277 q = 0) : d336209 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334277, d336209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34895 q selected
    | true =>
      simp only [d334277, d336209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334278 q = 0) : d336210 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334278, d336210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334278, d336210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334283 q = 0) : d336215 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334283, d336215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334283, d336215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334317 q = 0) : d336249 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334317, d336249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334317, d336249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334318 q = 0) : d336250 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334318, d336250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334318, d336250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334437 q = 0) : d336313 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334437, d336313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334437, d336313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34930 (p : Pattern) (selected : d334441 p = 0) : d336317 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334347 q = 0) : d336279 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334347, d336279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34910 q selected
    | true =>
      simp only [d334347, d336279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334348 q = 0) : d336280 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334348, d336280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334348, d336280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334273 q = 0) : d336205 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334273, d336205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34894 q selected
    | true =>
      simp only [d334273, d336205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334274 q = 0) : d336206 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334274, d336206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334274, d336206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334349 q = 0) : d336281 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334349, d336281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334349, d336281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334350 q = 0) : d336282 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334350, d336282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334350, d336282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334351 q = 0) : d336283 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334351, d336283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334351, d336283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334441 q = 0) : d336317 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334441, d336317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334441, d336317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro34931 (p : Pattern) (selected : d334443 p = 0) : d336227 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334395 q = 0) : d336205 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334395, d336205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34918 q selected
    | true =>
      simp only [d334395, d336205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334396 q = 0) : d336206 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334396, d336206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334396, d336206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334399 q = 0) : d336209 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334399, d336209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34919 q selected
    | true =>
      simp only [d334399, d336209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334400 q = 0) : d336210 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334400, d336210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334400, d336210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334401 q = 0) : d336211 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334401, d336211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334401, d336211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334402 q = 0) : d336212 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334402, d336212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334402, d336212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334403 q = 0) : d336213 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334403, d336213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334403, d336213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334443 q = 0) : d336227 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334443, d336227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334443, d336227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro34932 (p : Pattern) (selected : d334444 p = 0) : d336228 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334399 q = 0) : d336209 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334399, d336209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34919 q selected
    | true =>
      simp only [d334399, d336209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334400 q = 0) : d336210 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334400, d336210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334400, d336210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334405 q = 0) : d336215 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334405, d336215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334405, d336215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334406 q = 0) : d336216 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334406, d336216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334406, d336216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334407 q = 0) : d336217 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334407, d336217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334407, d336217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334444 q = 0) : d336228 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334444, d336228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334444, d336228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34933 (p : Pattern) (selected : d334447 p = 0) : d336320 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334418 q = 0) : d336294 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334418, d336294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34923 q selected
    | true =>
      simp only [d334418, d336294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334419 q = 0) : d336295 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334419, d336295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334419, d336295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334420 q = 0) : d336296 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334420, d336296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334420, d336296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334421 q = 0) : d336297 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334421, d336297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334421, d336297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334422 q = 0) : d336298 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334422, d336298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334422, d336298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334447 q = 0) : d336320 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334447, d336320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334447, d336320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34934 (p : Pattern) (selected : d334453 p = 0) : d336326 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334310 q = 0) : d336242 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334310, d336242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34902 q selected
    | true =>
      simp only [d334310, d336242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34903 q selected
  have h2 (q : Pattern) (selected : d334311 q = 0) : d336243 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334311, d336243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334311, d336243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334312 q = 0) : d336244 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334312, d336244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334312, d336244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334313 q = 0) : d336245 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334313, d336245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334313, d336245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334320 q = 0) : d336252 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334320, d336252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34904 q selected
    | true =>
      simp only [d334320, d336252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34905 q selected
  have h6 (q : Pattern) (selected : d334321 q = 0) : d336253 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334321, d336253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334321, d336253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334322 q = 0) : d336254 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334322, d336254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334322, d336254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334353 q = 0) : d336285 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334353, d336285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34911 q selected
    | true =>
      simp only [d334353, d336285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34896 q selected
  have h9 (q : Pattern) (selected : d334409 q = 0) : d336219 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334409, d336219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34920 q selected
    | true =>
      simp only [d334409, d336219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34921 q selected
  have h10 (q : Pattern) (selected : d334410 q = 0) : d336286 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334410, d336286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d334410, d336286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d334424 q = 0) : d336300 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334424, d336300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34924 q selected
    | true =>
      simp only [d334424, d336300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d334425 q = 0) : d336301 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334425, d336301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d334425, d336301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d334426 q = 0) : d336302 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334426, d336302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d334426, d336302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d334427 q = 0) : d336303 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334427, d336303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334427, d336303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d334428 q = 0) : d336304 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334428, d336304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334428, d336304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d334432 q = 0) : d336308 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334432, d336308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34926 q selected
    | true =>
      simp only [d334432, d336308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34927 q selected
  have h17 (q : Pattern) (selected : d334433 q = 0) : d336309 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334433, d336309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334433, d336309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d334434 q = 0) : d336310 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334434, d336310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d334434, d336310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d334435 q = 0) : d336311 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334435, d336311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334435, d336311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d334438 q = 0) : d336314 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334438, d336314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34928 q selected
    | true =>
      simp only [d334438, d336314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34929 q selected
  have h21 (q : Pattern) (selected : d334439 q = 0) : d336315 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334439, d336315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334439, d336315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d334440 q = 0) : d336316 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334440, d336316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d334440, d336316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d334442 q = 0) : d336318 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334442, d336318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34930 q selected
    | true =>
      simp only [d334442, d336318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34899 q selected
  have h24 (q : Pattern) (selected : d334445 q = 0) : d336229 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334445, d336229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34931 q selected
    | true =>
      simp only [d334445, d336229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34932 q selected
  have h25 (q : Pattern) (selected : d334446 q = 0) : d336319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334446, d336319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d334446, d336319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d334448 q = 0) : d336321 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334448, d336321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34933 q selected
    | true =>
      simp only [d334448, d336321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d334449 q = 0) : d336322 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334449, d336322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d334449, d336322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d334450 q = 0) : d336323 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334450, d336323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d334450, d336323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d334451 q = 0) : d336324 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334451, d336324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d334451, d336324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d334452 q = 0) : d336325 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334452, d336325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d334452, d336325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d334453 q = 0) : d336326 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d334453, d336326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d334453, d336326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro34935 (p : Pattern) (selected : d334460 p = 0) : d336333 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334287 q = 0) : d336219 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334287, d336219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34896 q selected
    | true =>
      simp only [d334287, d336219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34897 q selected
  have h2 (q : Pattern) (selected : d334288 q = 0) : d336220 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334288, d336220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334288, d336220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334289 q = 0) : d336221 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334289, d336221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334289, d336221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334290 q = 0) : d336222 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334290, d336222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334290, d336222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334291 q = 0) : d336223 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334291, d336223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334291, d336223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334455 q = 0) : d336328 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334455, d336328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34897 q selected
    | true =>
      simp only [d334455, d336328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334456 q = 0) : d336329 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334456, d336329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334456, d336329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334457 q = 0) : d336330 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334457, d336330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334457, d336330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334458 q = 0) : d336331 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334458, d336331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334458, d336331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334459 q = 0) : d336332 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334459, d336332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334459, d336332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d334460 q = 0) : d336333 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d334460, d336333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334460, d336333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro34936 (p : Pattern) (selected : d334466 p = 0) : d336339 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334455 q = 0) : d336328 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334455, d336328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34897 q selected
    | true =>
      simp only [d334455, d336328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334456 q = 0) : d336329 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334456, d336329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334456, d336329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334457 q = 0) : d336330 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334457, d336330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334457, d336330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334458 q = 0) : d336331 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334458, d336331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334458, d336331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334459 q = 0) : d336332 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334459, d336332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334459, d336332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334461 q = 0) : d336334 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334461, d336334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34900 q selected
    | true =>
      simp only [d334461, d336334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334462 q = 0) : d336335 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334462, d336335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334462, d336335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334463 q = 0) : d336336 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334463, d336336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334463, d336336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334464 q = 0) : d336337 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334464, d336337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334464, d336337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334465 q = 0) : d336338 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334465, d336338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334465, d336338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d334466 q = 0) : d336339 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d334466, d336339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334466, d336339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro34937 (p : Pattern) (selected : d334473 p = 0) : d336346 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334442 q = 0) : d336318 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334442, d336318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34930 q selected
    | true =>
      simp only [d334442, d336318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34899 q selected
  have h2 (q : Pattern) (selected : d334445 q = 0) : d336229 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334445, d336229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34931 q selected
    | true =>
      simp only [d334445, d336229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34932 q selected
  have h3 (q : Pattern) (selected : d334446 q = 0) : d336319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334446, d336319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334446, d336319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334448 q = 0) : d336321 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334448, d336321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34933 q selected
    | true =>
      simp only [d334448, d336321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334449 q = 0) : d336322 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334449, d336322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334449, d336322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334450 q = 0) : d336323 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334450, d336323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334450, d336323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334471 q = 0) : d336344 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334471, d336344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334471, d336344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334472 q = 0) : d336345 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334472, d336345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334472, d336345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d334473 q = 0) : d336346 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d334473, d336346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334473, d336346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro34938 (p : Pattern) (selected : d334475 p = 0) : d336348 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334461 q = 0) : d336334 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334461, d336334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34900 q selected
    | true =>
      simp only [d334461, d336334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334462 q = 0) : d336335 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334462, d336335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334462, d336335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334463 q = 0) : d336336 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334463, d336336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334463, d336336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334464 q = 0) : d336337 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334464, d336337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334464, d336337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334465 q = 0) : d336338 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334465, d336338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334465, d336338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334475 q = 0) : d336348 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d334475, d336348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334475, d336348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro34939 (p : Pattern) (selected : d334490 p = 0) : d336363 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334481 q = 0) : d336354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334481, d336354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334481, d336354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34906 q selected
  have h2 (q : Pattern) (selected : d334326 q = 0) : d336258 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334326, d336258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34906 q selected
    | true =>
      simp only [d334326, d336258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334482 q = 0) : d336355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334482, d336355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334482, d336355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334327 q = 0) : d336259 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334327, d336259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334327, d336259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334483 q = 0) : d336356 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334483, d336356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334483, d336356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334484 q = 0) : d336357 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334484, d336357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334484, d336357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334485 q = 0) : d336358 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334485, d336358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334485, d336358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34907 q selected
  have h8 (q : Pattern) (selected : d334331 q = 0) : d336263 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334331, d336263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34907 q selected
    | true =>
      simp only [d334331, d336263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334486 q = 0) : d336359 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334486, d336359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334486, d336359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334332 q = 0) : d336264 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334332, d336264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d334332, d336264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d334487 q = 0) : d336360 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334487, d336360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334487, d336360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d334488 q = 0) : d336361 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334488, d336361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d334488, d336361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d334489 q = 0) : d336362 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334489, d336362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334489, d336362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d334490 q = 0) : d336363 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334490, d336363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d334490, d336363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h14 p selected
theorem eqIntro34940 (p : Pattern) (selected : d334496 p = 0) : d336369 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334126 q = 0) : d336094 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334126, d336094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334126, d336094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34840 q selected
  have h2 (q : Pattern) (selected : d333994 q = 0) : d336007 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333994, d336007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34840 q selected
    | true =>
      simp only [d333994, d336007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334127 q = 0) : d336095 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334127, d336095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334127, d336095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333995 q = 0) : d336008 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333995, d336008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333995, d336008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334128 q = 0) : d336096 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334128, d336096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334128, d336096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334129 q = 0) : d336097 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334129, d336097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334129, d336097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334130 q = 0) : d336098 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334130, d336098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334130, d336098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34841 q selected
  have h8 (q : Pattern) (selected : d333999 q = 0) : d336012 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333999, d336012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34841 q selected
    | true =>
      simp only [d333999, d336012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334131 q = 0) : d336099 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334131, d336099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334131, d336099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334000 q = 0) : d336013 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334000, d336013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d334000, d336013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d334132 q = 0) : d336100 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334132, d336100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334132, d336100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d334133 q = 0) : d336101 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334133, d336101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d334133, d336101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d334134 q = 0) : d336102 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334134, d336102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334134, d336102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d334491 q = 0) : d336364 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334491, d336364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334491, d336364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34890 q selected
  have h15 (q : Pattern) (selected : d334252 q = 0) : d336184 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334252, d336184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34890 q selected
    | true =>
      simp only [d334252, d336184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d334492 q = 0) : d336365 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334492, d336365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d334492, d336365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d334253 q = 0) : d336185 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334253, d336185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d334253, d336185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d334493 q = 0) : d336366 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334493, d336366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d334493, d336366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d334494 q = 0) : d336367 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334494, d336367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d334494, d336367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d334495 q = 0) : d336368 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334495, d336368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334495, d336368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d334496 q = 0) : d336369 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334496, d336369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d334496, d336369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro34941 (p : Pattern) (selected : d334501 p = 0) : d336374 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334491 q = 0) : d336364 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334491, d336364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334491, d336364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34890 q selected
  have h2 (q : Pattern) (selected : d334252 q = 0) : d336184 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334252, d336184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34890 q selected
    | true =>
      simp only [d334252, d336184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334492 q = 0) : d336365 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334492, d336365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334492, d336365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334253 q = 0) : d336185 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334253, d336185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334253, d336185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334493 q = 0) : d336366 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334493, d336366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334493, d336366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334494 q = 0) : d336367 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334494, d336367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334494, d336367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334495 q = 0) : d336368 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334495, d336368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334495, d336368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334500 q = 0) : d336373 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334500, d336373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334500, d336373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334501 q = 0) : d336374 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334501, d336374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334501, d336374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro34942 (p : Pattern) (selected : d334507 p = 0) : d336380 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333849 q = 0) : d335881 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333849, d335881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333849, d335881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34795 q selected
  have h2 (q : Pattern) (selected : d333751 q = 0) : d335808 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333751, d335808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34795 q selected
    | true =>
      simp only [d333751, d335808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333850 q = 0) : d335882 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333850, d335882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333850, d335882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333752 q = 0) : d335809 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333752, d335809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333752, d335809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333851 q = 0) : d335883 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333851, d335883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333851, d335883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333852 q = 0) : d335884 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333852, d335884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333852, d335884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333665 q = 0) : d335741 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333665, d335741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333665, d335741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34766 q selected
  have h8 (q : Pattern) (selected : d333586 q = 0) : d335687 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333586, d335687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34766 q selected
    | true =>
      simp only [d333586, d335687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d333666 q = 0) : d335742 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333666, d335742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333666, d335742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333587 q = 0) : d335688 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333587, d335688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d333587, d335688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d333667 q = 0) : d335743 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333667, d335743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d333667, d335743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d333668 q = 0) : d335744 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333668, d335744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d333668, d335744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d334506 q = 0) : d336379 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334506, d336379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334506, d336379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d334491 q = 0) : d336364 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334491, d336364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334491, d336364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34890 q selected
  have h15 (q : Pattern) (selected : d334252 q = 0) : d336184 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334252, d336184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34890 q selected
    | true =>
      simp only [d334252, d336184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d334492 q = 0) : d336365 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334492, d336365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d334492, d336365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d334253 q = 0) : d336185 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334253, d336185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d334253, d336185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d334493 q = 0) : d336366 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334493, d336366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d334493, d336366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d334494 q = 0) : d336367 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334494, d336367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d334494, d336367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d334500 q = 0) : d336373 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334500, d336373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d334500, d336373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d334507 q = 0) : d336380 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334507, d336380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d334507, d336380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro34943 (p : Pattern) (selected : d334512 p = 0) : d336385 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333665 q = 0) : d335741 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333665, d335741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333665, d335741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34766 q selected
  have h2 (q : Pattern) (selected : d333586 q = 0) : d335687 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333586, d335687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34766 q selected
    | true =>
      simp only [d333586, d335687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333666 q = 0) : d335742 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333666, d335742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333666, d335742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333587 q = 0) : d335688 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333587, d335688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333587, d335688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333667 q = 0) : d335743 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333667, d335743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333667, d335743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333668 q = 0) : d335744 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333668, d335744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333668, d335744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334511 q = 0) : d336384 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334511, d336384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334511, d336384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d333520 q = 0) : d335621 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333520, d335621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333520, d335621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34749 q selected
  have h9 (q : Pattern) (selected : d333479 q = 0) : d335580 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333479, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34749 q selected
    | true =>
      simp only [d333479, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d333521 q = 0) : d335622 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333521, d335622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d333521, d335622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d333480 q = 0) : d335581 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333480, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d333480, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d333522 q = 0) : d335623 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333522, d335623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d333522, d335623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d333523 q = 0) : d335624 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333523, d335624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d333523, d335624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d333524 q = 0) : d335625 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d333524, d335625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d333524, d335625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d334512 q = 0) : d336385 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334512, d336385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334512, d336385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro34944 (p : Pattern) (selected : d334518 p = 0) : d336391 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334497 q = 0) : d336370 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334497, d336370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34939 q selected
    | true =>
      simp only [d334497, d336370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34940 q selected
  have h2 (q : Pattern) (selected : d334498 q = 0) : d336371 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334498, d336371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334498, d336371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334499 q = 0) : d336372 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334499, d336372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334499, d336372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334502 q = 0) : d336375 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334502, d336375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34940 q selected
    | true =>
      simp only [d334502, d336375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34941 q selected
  have h5 (q : Pattern) (selected : d334503 q = 0) : d336376 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334503, d336376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334503, d336376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334504 q = 0) : d336377 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334504, d336377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334504, d336377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334505 q = 0) : d336378 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334505, d336378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334505, d336378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334508 q = 0) : d336381 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334508, d336381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34940 q selected
    | true =>
      simp only [d334508, d336381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34942 q selected
  have h9 (q : Pattern) (selected : d334509 q = 0) : d336382 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334509, d336382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334509, d336382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334510 q = 0) : d336383 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334510, d336383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334510, d336383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d334513 q = 0) : d336386 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334513, d336386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34942 q selected
    | true =>
      simp only [d334513, d336386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34943 q selected
  have h12 (q : Pattern) (selected : d334514 q = 0) : d336387 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334514, d336387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334514, d336387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d334515 q = 0) : d336388 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334515, d336388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334515, d336388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d334516 q = 0) : d336389 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334516, d336389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d334516, d336389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d334517 q = 0) : d336390 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334517, d336390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334517, d336390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d334518 q = 0) : d336391 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334518, d336391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d334518, d336391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro34945 (p : Pattern) (selected : d334523 p = 0) : d336396 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334508 q = 0) : d336381 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334508, d336381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34940 q selected
    | true =>
      simp only [d334508, d336381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34942 q selected
  have h2 (q : Pattern) (selected : d334509 q = 0) : d336382 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334509, d336382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334509, d336382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334510 q = 0) : d336383 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334510, d336383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334510, d336383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334513 q = 0) : d336386 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334513, d336386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34942 q selected
    | true =>
      simp only [d334513, d336386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34943 q selected
  have h5 (q : Pattern) (selected : d334514 q = 0) : d336387 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334514, d336387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334514, d336387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334515 q = 0) : d336388 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334515, d336388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334515, d336388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334516 q = 0) : d336389 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334516, d336389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334516, d336389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334521 q = 0) : d336394 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334521, d336394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334521, d336394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334522 q = 0) : d336395 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334522, d336395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334522, d336395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334523 q = 0) : d336396 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334523, d336396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334523, d336396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro34946 (p : Pattern) (selected : d334529 p = 0) : d336402 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334519 q = 0) : d336392 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334519, d336392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34944 q selected
    | true =>
      simp only [d334519, d336392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334520 q = 0) : d336393 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334520, d336393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334520, d336393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334524 q = 0) : d336397 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334524, d336397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34945 q selected
    | true =>
      simp only [d334524, d336397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334525 q = 0) : d336398 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334525, d336398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334525, d336398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334526 q = 0) : d336399 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334526, d336399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334526, d336399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334527 q = 0) : d336400 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334527, d336400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334527, d336400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334528 q = 0) : d336401 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334528, d336401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334528, d336401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334529 q = 0) : d336402 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334529, d336402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334529, d336402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro34947 (p : Pattern) (selected : d334531 p = 0) : d336404 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334513 q = 0) : d336386 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334513, d336386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34942 q selected
    | true =>
      simp only [d334513, d336386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34943 q selected
  have h2 (q : Pattern) (selected : d334514 q = 0) : d336387 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334514, d336387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334514, d336387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334515 q = 0) : d336388 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334515, d336388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334515, d336388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334521 q = 0) : d336394 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334521, d336394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334521, d336394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334530 q = 0) : d336403 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334530, d336403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334530, d336403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334531 q = 0) : d336404 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334531, d336404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334531, d336404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34948 (p : Pattern) (selected : d334537 p = 0) : d336410 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334524 q = 0) : d336397 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334524, d336397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34945 q selected
    | true =>
      simp only [d334524, d336397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334525 q = 0) : d336398 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334525, d336398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334525, d336398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334532 q = 0) : d336405 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334532, d336405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34947 q selected
    | true =>
      simp only [d334532, d336405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334533 q = 0) : d336406 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334533, d336406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334533, d336406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334534 q = 0) : d336407 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334534, d336407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334534, d336407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334535 q = 0) : d336408 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334535, d336408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334535, d336408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334536 q = 0) : d336409 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334536, d336409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334536, d336409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334537 q = 0) : d336410 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334537, d336410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334537, d336410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro34949 (p : Pattern) (selected : d334553 p = 0) : d336369 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334539 q = 0) : d336094 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334539, d336094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334539, d336094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34912 q selected
  have h2 (q : Pattern) (selected : d334361 q = 0) : d336007 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334361, d336007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34912 q selected
    | true =>
      simp only [d334361, d336007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334540 q = 0) : d336095 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334540, d336095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334540, d336095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334362 q = 0) : d336008 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334362, d336008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334362, d336008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334541 q = 0) : d336096 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334541, d336096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334541, d336096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334542 q = 0) : d336097 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334542, d336097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334542, d336097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334543 q = 0) : d336098 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334543, d336098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334543, d336098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34913 q selected
  have h8 (q : Pattern) (selected : d334366 q = 0) : d336012 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334366, d336012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34913 q selected
    | true =>
      simp only [d334366, d336012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334544 q = 0) : d336099 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334544, d336099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334544, d336099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334367 q = 0) : d336013 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334367, d336013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d334367, d336013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d334545 q = 0) : d336100 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334545, d336100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334545, d336100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d334546 q = 0) : d336101 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334546, d336101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d334546, d336101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d334547 q = 0) : d336102 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334547, d336102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334547, d336102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d334548 q = 0) : d336364 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334548, d336364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334548, d336364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34914 q selected
  have h15 (q : Pattern) (selected : d334374 q = 0) : d336184 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334374, d336184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34914 q selected
    | true =>
      simp only [d334374, d336184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d334549 q = 0) : d336365 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334549, d336365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d334549, d336365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d334375 q = 0) : d336185 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334375, d336185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d334375, d336185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d334550 q = 0) : d336366 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334550, d336366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d334550, d336366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d334551 q = 0) : d336367 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334551, d336367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d334551, d336367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d334552 q = 0) : d336368 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334552, d336368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334552, d336368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d334553 q = 0) : d336369 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334553, d336369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d334553, d336369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro34950 (p : Pattern) (selected : d334556 p = 0) : d336380 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334176 q = 0) : d335881 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334176, d335881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334176, d335881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34846 q selected
  have h2 (q : Pattern) (selected : d334026 q = 0) : d335808 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334026, d335808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34846 q selected
    | true =>
      simp only [d334026, d335808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334177 q = 0) : d335882 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334177, d335882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334177, d335882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334027 q = 0) : d335809 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334027, d335809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334027, d335809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334178 q = 0) : d335883 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334178, d335883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334178, d335883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334179 q = 0) : d335884 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334179, d335884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334179, d335884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d333875 q = 0) : d335741 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333875, d335741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333875, d335741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34800 q selected
  have h8 (q : Pattern) (selected : d333782 q = 0) : d335687 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333782, d335687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34800 q selected
    | true =>
      simp only [d333782, d335687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d333876 q = 0) : d335742 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333876, d335742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d333876, d335742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d333783 q = 0) : d335688 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333783, d335688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d333783, d335688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d333877 q = 0) : d335743 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333877, d335743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d333877, d335743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d333878 q = 0) : d335744 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333878, d335744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d333878, d335744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d334554 q = 0) : d336379 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334554, d336379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334554, d336379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d334548 q = 0) : d336364 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334548, d336364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334548, d336364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34914 q selected
  have h15 (q : Pattern) (selected : d334374 q = 0) : d336184 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334374, d336184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34914 q selected
    | true =>
      simp only [d334374, d336184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d334549 q = 0) : d336365 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334549, d336365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d334549, d336365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d334375 q = 0) : d336185 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334375, d336185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d334375, d336185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d334550 q = 0) : d336366 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334550, d336366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d334550, d336366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d334551 q = 0) : d336367 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334551, d336367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d334551, d336367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d334555 q = 0) : d336373 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334555, d336373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d334555, d336373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d334556 q = 0) : d336380 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334556, d336380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d334556, d336380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro34951 (p : Pattern) (selected : d334561 p = 0) : d336385 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333875 q = 0) : d335741 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333875, d335741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333875, d335741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34800 q selected
  have h2 (q : Pattern) (selected : d333782 q = 0) : d335687 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333782, d335687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34800 q selected
    | true =>
      simp only [d333782, d335687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333876 q = 0) : d335742 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333876, d335742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333876, d335742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333783 q = 0) : d335688 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333783, d335688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333783, d335688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333877 q = 0) : d335743 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333877, d335743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333877, d335743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333878 q = 0) : d335744 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333878, d335744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333878, d335744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334560 q = 0) : d336384 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334560, d336384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334560, d336384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d333684 q = 0) : d335621 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333684, d335621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333684, d335621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34770 q selected
  have h9 (q : Pattern) (selected : d333609 q = 0) : d335580 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333609, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34770 q selected
    | true =>
      simp only [d333609, d335580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d333685 q = 0) : d335622 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333685, d335622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d333685, d335622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d333610 q = 0) : d335581 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333610, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d333610, d335581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d333686 q = 0) : d335623 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333686, d335623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d333686, d335623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d333687 q = 0) : d335624 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333687, d335624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d333687, d335624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d333688 q = 0) : d335625 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d333688, d335625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d333688, d335625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d334561 q = 0) : d336385 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334561, d336385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334561, d336385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro34952 (p : Pattern) (selected : d334568 p = 0) : d336396 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334557 q = 0) : d336381 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334557, d336381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34949 q selected
    | true =>
      simp only [d334557, d336381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34950 q selected
  have h2 (q : Pattern) (selected : d334558 q = 0) : d336382 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334558, d336382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334558, d336382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334559 q = 0) : d336383 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334559, d336383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334559, d336383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334562 q = 0) : d336386 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334562, d336386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34950 q selected
    | true =>
      simp only [d334562, d336386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34951 q selected
  have h5 (q : Pattern) (selected : d334563 q = 0) : d336387 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334563, d336387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334563, d336387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334564 q = 0) : d336388 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334564, d336388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334564, d336388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334565 q = 0) : d336389 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334565, d336389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334565, d336389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334566 q = 0) : d336394 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334566, d336394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334566, d336394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334567 q = 0) : d336395 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334567, d336395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334567, d336395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334568 q = 0) : d336396 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334568, d336396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334568, d336396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro34953 (p : Pattern) (selected : d334572 p = 0) : d336404 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334562 q = 0) : d336386 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334562, d336386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34950 q selected
    | true =>
      simp only [d334562, d336386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34951 q selected
  have h2 (q : Pattern) (selected : d334563 q = 0) : d336387 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334563, d336387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334563, d336387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334564 q = 0) : d336388 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334564, d336388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334564, d336388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334566 q = 0) : d336394 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334566, d336394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334566, d336394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334571 q = 0) : d336403 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334571, d336403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334571, d336403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334572 q = 0) : d336404 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334572, d336404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334572, d336404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34954 (p : Pattern) (selected : d334578 p = 0) : d336410 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334569 q = 0) : d336397 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334569, d336397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34952 q selected
    | true =>
      simp only [d334569, d336397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334570 q = 0) : d336398 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334570, d336398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334570, d336398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334573 q = 0) : d336405 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334573, d336405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34953 q selected
    | true =>
      simp only [d334573, d336405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334574 q = 0) : d336406 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334574, d336406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334574, d336406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334575 q = 0) : d336407 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334575, d336407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334575, d336407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334576 q = 0) : d336408 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334576, d336408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334576, d336408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334577 q = 0) : d336409 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334577, d336409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334577, d336409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334578 q = 0) : d336410 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334578, d336410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334578, d336410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro34955 (p : Pattern) (selected : d334582 p = 0) : d336415 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334573 q = 0) : d336405 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334573, d336405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34953 q selected
    | true =>
      simp only [d334573, d336405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334574 q = 0) : d336406 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334574, d336406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334574, d336406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334579 q = 0) : d336412 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334579, d336412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334579, d336412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334580 q = 0) : d336413 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334580, d336413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334580, d336413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334581 q = 0) : d336414 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334581, d336414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334581, d336414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334582 q = 0) : d336415 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334582, d336415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334582, d336415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34956 (p : Pattern) (selected : d334585 p = 0) : d336418 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333665 q = 0) : d335741 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333665, d335741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d333665, d335741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34766 q selected
  have h2 (q : Pattern) (selected : d333586 q = 0) : d335687 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d333586, d335687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34766 q selected
    | true =>
      simp only [d333586, d335687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d333666 q = 0) : d335742 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333666, d335742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d333666, d335742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d333587 q = 0) : d335688 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d333587, d335688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333587, d335688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d333667 q = 0) : d335743 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d333667, d335743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d333667, d335743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d333668 q = 0) : d335744 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d333668, d335744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d333668, d335744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334511 q = 0) : d336384 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334511, d336384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334511, d336384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334585 q = 0) : d336418 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334585, d336418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334585, d336418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro34957 (p : Pattern) (selected : d334591 p = 0) : d336424 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334508 q = 0) : d336381 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334508, d336381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34940 q selected
    | true =>
      simp only [d334508, d336381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34942 q selected
  have h2 (q : Pattern) (selected : d334509 q = 0) : d336382 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334509, d336382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334509, d336382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334510 q = 0) : d336383 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334510, d336383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334510, d336383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334513 q = 0) : d336386 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334513, d336386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34942 q selected
    | true =>
      simp only [d334513, d336386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34943 q selected
  have h5 (q : Pattern) (selected : d334514 q = 0) : d336387 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334514, d336387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334514, d336387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334515 q = 0) : d336388 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334515, d336388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334515, d336388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334516 q = 0) : d336389 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334516, d336389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334516, d336389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334586 q = 0) : d336419 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334586, d336419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34942 q selected
    | true =>
      simp only [d334586, d336419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34956 q selected
  have h9 (q : Pattern) (selected : d334587 q = 0) : d336420 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334587, d336420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334587, d336420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334588 q = 0) : d336421 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334588, d336421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334588, d336421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d334589 q = 0) : d336422 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334589, d336422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d334589, d336422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d334590 q = 0) : d336423 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334590, d336423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334590, d336423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d334591 q = 0) : d336424 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334591, d336424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d334591, d336424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro34958 (p : Pattern) (selected : d334597 p = 0) : d336430 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334592 q = 0) : d336425 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334592, d336425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34957 q selected
    | true =>
      simp only [d334592, d336425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334593 q = 0) : d336426 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334593, d336426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334593, d336426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334594 q = 0) : d336427 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334594, d336427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334594, d336427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334595 q = 0) : d336428 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334595, d336428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334595, d336428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334596 q = 0) : d336429 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334596, d336429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334596, d336429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334597 q = 0) : d336430 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334597, d336430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334597, d336430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34959 (p : Pattern) (selected : d334603 p = 0) : d336436 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334538 q = 0) : d336411 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334538, d336411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34946 q selected
    | true =>
      simp only [d334538, d336411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34948 q selected
  have h2 (q : Pattern) (selected : d334583 q = 0) : d336416 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334583, d336416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34954 q selected
    | true =>
      simp only [d334583, d336416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34955 q selected
  have h3 (q : Pattern) (selected : d334584 q = 0) : d336417 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334584, d336417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334584, d336417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334598 q = 0) : d336431 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334598, d336431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34958 q selected
    | true =>
      simp only [d334598, d336431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334599 q = 0) : d336432 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334599, d336432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334599, d336432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334600 q = 0) : d336433 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334600, d336433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334600, d336433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334601 q = 0) : d336434 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334601, d336434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334601, d336434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334602 q = 0) : d336435 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334602, d336435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334602, d336435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d334603 q = 0) : d336436 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d334603, d336436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334603, d336436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro34960 (p : Pattern) (selected : d334608 p = 0) : d336415 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334532 q = 0) : d336405 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334532, d336405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34947 q selected
    | true =>
      simp only [d334532, d336405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334533 q = 0) : d336406 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334533, d336406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334533, d336406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334605 q = 0) : d336412 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334605, d336412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334605, d336412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334606 q = 0) : d336413 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334606, d336413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334606, d336413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334607 q = 0) : d336414 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334607, d336414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334607, d336414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334608 q = 0) : d336415 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334608, d336415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334608, d336415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34961 (p : Pattern) (selected : d334614 p = 0) : d336443 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334609 q = 0) : d336438 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334609, d336438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34960 q selected
    | true =>
      simp only [d334609, d336438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334610 q = 0) : d336439 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334610, d336439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334610, d336439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334611 q = 0) : d336440 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334611, d336440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334611, d336440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334612 q = 0) : d336441 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334612, d336441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334612, d336441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334613 q = 0) : d336442 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334613, d336442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334613, d336442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334614 q = 0) : d336443 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d334614, d336443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334614, d336443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro34962 (p : Pattern) (selected : d334620 p = 0) : d336449 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334293 q = 0) : d336225 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d334293, d336225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334293, d336225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34898 q selected
  have h2 (q : Pattern) (selected : d334294 q = 0) : d336226 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d334294, d336226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334294, d336226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334303 q = 0) : d336235 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d334303, d336235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34898 q selected
    | true =>
      simp only [d334303, d336235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34901 q selected
  have h4 (q : Pattern) (selected : d334304 q = 0) : d336236 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d334304, d336236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334304, d336236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334305 q = 0) : d336237 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d334305, d336237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334305, d336237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334454 q = 0) : d336327 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d334454, d336327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34925 q selected
    | true =>
      simp only [d334454, d336327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34934 q selected
  have h7 (q : Pattern) (selected : d334467 q = 0) : d336340 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d334467, d336340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34935 q selected
    | true =>
      simp only [d334467, d336340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34936 q selected
  have h8 (q : Pattern) (selected : d334468 q = 0) : d336341 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d334468, d336341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334468, d336341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d334469 q = 0) : d336342 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d334469, d336342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d334469, d336342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d334470 q = 0) : d336343 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d334470, d336343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334470, d336343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d334474 q = 0) : d336347 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d334474, d336347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334474, d336347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34937 q selected
  have h12 (q : Pattern) (selected : d334476 q = 0) : d336349 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d334476, d336349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334476, d336349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34938 q selected
  have h13 (q : Pattern) (selected : d334477 q = 0) : d336350 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d334477, d336350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d334477, d336350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d334478 q = 0) : d336351 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d334478, d336351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d334478, d336351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d334479 q = 0) : d336352 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d334479, d336352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d334479, d336352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d334480 q = 0) : d336353 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d334480, d336353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d334480, d336353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d334604 q = 0) : d336437 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d334604, d336437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334604, d336437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34959 q selected
  have h18 (q : Pattern) (selected : d334615 q = 0) : d336444 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d334615, d336444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334615, d336444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34961 q selected
  have h19 (q : Pattern) (selected : d334616 q = 0) : d336445 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d334616, d336445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d334616, d336445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d334617 q = 0) : d336446 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d334617, d336446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d334617, d336446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d334618 q = 0) : d336447 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d334618, d336447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d334618, d336447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d334619 q = 0) : d336448 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d334619, d336448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d334619, d336448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d334620 q = 0) : d336449 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d334620, d336449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d334620, d336449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro34963 (p : Pattern) (selected : d334626 p = 0) : d336455 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334621 q = 0) : d336450 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d334621, d336450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334621, d336450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34962 q selected
  have h2 (q : Pattern) (selected : d334622 q = 0) : d336451 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d334622, d336451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334622, d336451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334623 q = 0) : d336452 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d334623, d336452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334623, d336452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334624 q = 0) : d336453 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d334624, d336453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334624, d336453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334625 q = 0) : d336454 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d334625, d336454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334625, d336454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334626 q = 0) : d336455 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d334626, d336455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334626, d336455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro34964 (p : Pattern) (selected : d334633 p = 0) : d336462 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334630 q = 0) : d336459 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334630, d336459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro465 q selected
    | true =>
      simp only [d334630, d336459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334631 q = 0) : d336460 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334631, d336460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334631, d336460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334632 q = 0) : d336461 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334632, d336461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334632, d336461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334633 q = 0) : d336462 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d334633, d336462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334633, d336462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h4 p selected
theorem eqIntro34965 (p : Pattern) (selected : d334640 p = 0) : d336469 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333987 q = 0) : d336000 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333987, d336000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23519 q selected
    | true =>
      simp only [d333987, d336000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334630 q = 0) : d336459 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334630, d336459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro465 q selected
    | true =>
      simp only [d334630, d336459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334638 q = 0) : d336467 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334638, d336467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334638, d336467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334639 q = 0) : d336468 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334639, d336468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334639, d336468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334640 q = 0) : d336469 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d334640, d336469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334640, d336469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro34966 (p : Pattern) (selected : d334651 p = 0) : d336480 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334630 q = 0) : d336459 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334630, d336459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro465 q selected
    | true =>
      simp only [d334630, d336459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334646 q = 0) : d336475 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334646, d336475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334646, d336475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334647 q = 0) : d336476 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334647, d336476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334647, d336476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334648 q = 0) : d336477 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334648, d336477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro467 q selected
    | true =>
      simp only [d334648, d336477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
  have h5 (q : Pattern) (selected : d334649 q = 0) : d336478 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334649, d336478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334649, d336478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334650 q = 0) : d336479 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334650, d336479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334650, d336479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334651 q = 0) : d336480 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d334651, d336480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334651, d336480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro34967 (p : Pattern) (selected : d334657 p = 0) : d336486 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334634 q = 0) : d336463 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334634, d336463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34964 q selected
    | true =>
      simp only [d334634, d336463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334635 q = 0) : d336464 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334635, d336464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334635, d336464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334636 q = 0) : d336465 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334636, d336465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334636, d336465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334637 q = 0) : d336466 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334637, d336466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334637, d336466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334641 q = 0) : d336470 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334641, d336470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34965 q selected
    | true =>
      simp only [d334641, d336470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334642 q = 0) : d336471 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334642, d336471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334642, d336471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334643 q = 0) : d336472 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334643, d336472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334643, d336472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334644 q = 0) : d336473 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334644, d336473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334644, d336473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334645 q = 0) : d336474 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334645, d336474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334645, d336474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334652 q = 0) : d336481 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334652, d336481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34966 q selected
    | true =>
      simp only [d334652, d336481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d334653 q = 0) : d336482 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334653, d336482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d334653, d336482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d334654 q = 0) : d336483 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334654, d336483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334654, d336483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d334655 q = 0) : d336484 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334655, d336484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d334655, d336484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d334656 q = 0) : d336485 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334656, d336485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334656, d336485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d334657 q = 0) : d336486 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334657, d336486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334657, d336486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro34968 (p : Pattern) (selected : d334661 p = 0) : d336490 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d333987 q = 0) : d336000 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d333987, d336000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23519 q selected
    | true =>
      simp only [d333987, d336000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334630 q = 0) : d336459 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334630, d336459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro465 q selected
    | true =>
      simp only [d334630, d336459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334638 q = 0) : d336467 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334638, d336467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334638, d336467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334639 q = 0) : d336468 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334639, d336468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334639, d336468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334658 q = 0) : d336487 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334658, d336487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro468 q selected
    | true =>
      simp only [d334658, d336487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334659 q = 0) : d336488 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334659, d336488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334659, d336488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334660 q = 0) : d336489 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334660, d336489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334660, d336489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334661 q = 0) : d336490 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d334661, d336490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334661, d336490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro34969 (p : Pattern) (selected : d334666 p = 0) : d336495 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334630 q = 0) : d336459 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334630, d336459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro465 q selected
    | true =>
      simp only [d334630, d336459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334658 q = 0) : d336487 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334658, d336487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro468 q selected
    | true =>
      simp only [d334658, d336487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334659 q = 0) : d336488 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334659, d336488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334659, d336488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334660 q = 0) : d336489 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334660, d336489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334660, d336489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334648 q = 0) : d336477 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334648, d336477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro467 q selected
    | true =>
      simp only [d334648, d336477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
  have h6 (q : Pattern) (selected : d334649 q = 0) : d336478 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334649, d336478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334649, d336478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334650 q = 0) : d336479 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334650, d336479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334650, d336479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334666 q = 0) : d336495 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d334666, d336495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334666, d336495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro34970 (p : Pattern) (selected : d334673 p = 0) : d336502 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334662 q = 0) : d336491 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334662, d336491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34968 q selected
    | true =>
      simp only [d334662, d336491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334663 q = 0) : d336492 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334663, d336492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334663, d336492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334664 q = 0) : d336493 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334664, d336493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334664, d336493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334665 q = 0) : d336494 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334665, d336494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334665, d336494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334667 q = 0) : d336496 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334667, d336496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34969 q selected
    | true =>
      simp only [d334667, d336496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334668 q = 0) : d336497 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334668, d336497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334668, d336497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334669 q = 0) : d336498 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334669, d336498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334669, d336498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334670 q = 0) : d336499 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334670, d336499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334670, d336499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334671 q = 0) : d336500 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334671, d336500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334671, d336500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334652 q = 0) : d336481 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334652, d336481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34966 q selected
    | true =>
      simp only [d334652, d336481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d334653 q = 0) : d336482 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334653, d336482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d334653, d336482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d334654 q = 0) : d336483 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334654, d336483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334654, d336483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d334655 q = 0) : d336484 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334655, d336484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d334655, d336484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d334672 q = 0) : d336501 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334672, d336501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d334672, d336501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d334673 q = 0) : d336502 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334673, d336502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334673, d336502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro34971 (p : Pattern) (selected : d334678 p = 0) : d336507 p = 1 := by
  have h0 (q : Pattern) (selected : d334648 q = 0) : d336477 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334648, d336477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro467 q selected
    | true =>
      simp only [d334648, d336477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d334649 q = 0) : d336478 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334649, d336478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334649, d336478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334650 q = 0) : d336479 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334650, d336479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334650, d336479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d334678 q = 0) : d336507 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d334678, d336507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334678, d336507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h4 p selected
theorem eqIntro34972 (p : Pattern) (selected : d334684 p = 0) : d336513 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334667 q = 0) : d336496 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334667, d336496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34969 q selected
    | true =>
      simp only [d334667, d336496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334668 q = 0) : d336497 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334668, d336497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334668, d336497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334669 q = 0) : d336498 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334669, d336498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334669, d336498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334670 q = 0) : d336499 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334670, d336499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334670, d336499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334677 q = 0) : d336506 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334677, d336506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334677, d336506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334679 q = 0) : d336508 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334679, d336508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34971 q selected
    | true =>
      simp only [d334679, d336508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334680 q = 0) : d336509 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334680, d336509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334680, d336509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334681 q = 0) : d336510 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334681, d336510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334681, d336510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d334682 q = 0) : d336511 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334682, d336511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d334682, d336511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d334683 q = 0) : d336512 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334683, d336512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334683, d336512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d334684 q = 0) : d336513 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334684, d336513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334684, d336513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro34973 (p : Pattern) (selected : d334691 p = 0) : d336520 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334674 q = 0) : d336503 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334674, d336503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34967 q selected
    | true =>
      simp only [d334674, d336503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34970 q selected
  have h2 (q : Pattern) (selected : d334675 q = 0) : d336504 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334675, d336504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334675, d336504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334676 q = 0) : d336505 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334676, d336505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334676, d336505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334685 q = 0) : d336514 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334685, d336514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34970 q selected
    | true =>
      simp only [d334685, d336514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34972 q selected
  have h5 (q : Pattern) (selected : d334686 q = 0) : d336515 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334686, d336515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334686, d336515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334687 q = 0) : d336516 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334687, d336516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334687, d336516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334688 q = 0) : d336517 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334688, d336517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334688, d336517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334689 q = 0) : d336518 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334689, d336518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334689, d336518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334690 q = 0) : d336519 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334690, d336519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334690, d336519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334691 q = 0) : d336520 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334691, d336520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334691, d336520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro34974 (p : Pattern) (selected : d334695 p = 0) : d336524 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334685 q = 0) : d336514 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334685, d336514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34970 q selected
    | true =>
      simp only [d334685, d336514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34972 q selected
  have h2 (q : Pattern) (selected : d334686 q = 0) : d336515 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334686, d336515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334686, d336515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334687 q = 0) : d336516 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334687, d336516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334687, d336516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334689 q = 0) : d336518 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334689, d336518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334689, d336518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334694 q = 0) : d336523 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334694, d336523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334694, d336523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334695 q = 0) : d336524 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334695, d336524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334695, d336524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34975 (p : Pattern) (selected : d334701 p = 0) : d336530 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334692 q = 0) : d336521 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334692, d336521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34973 q selected
    | true =>
      simp only [d334692, d336521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334693 q = 0) : d336522 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334693, d336522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334693, d336522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334696 q = 0) : d336525 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334696, d336525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34974 q selected
    | true =>
      simp only [d334696, d336525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334697 q = 0) : d336526 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334697, d336526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334697, d336526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334698 q = 0) : d336527 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334698, d336527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334698, d336527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334699 q = 0) : d336528 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334699, d336528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334699, d336528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334700 q = 0) : d336529 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334700, d336529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334700, d336529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334701 q = 0) : d336530 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334701, d336530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334701, d336530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro34976 (p : Pattern) (selected : d334705 p = 0) : d336534 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334696 q = 0) : d336525 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334696, d336525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34974 q selected
    | true =>
      simp only [d334696, d336525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334697 q = 0) : d336526 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334697, d336526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334697, d336526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334702 q = 0) : d336531 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334702, d336531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334702, d336531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334703 q = 0) : d336532 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334703, d336532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334703, d336532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334704 q = 0) : d336533 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334704, d336533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334704, d336533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334705 q = 0) : d336534 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334705, d336534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334705, d336534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro34977 (p : Pattern) (selected : d334711 p = 0) : d336540 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334706 q = 0) : d336535 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334706, d336535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34975 q selected
    | true =>
      simp only [d334706, d336535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34976 q selected
  have h2 (q : Pattern) (selected : d334707 q = 0) : d336536 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334707, d336536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334707, d336536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334708 q = 0) : d336537 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334708, d336537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334708, d336537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334709 q = 0) : d336538 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334709, d336538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334709, d336538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334710 q = 0) : d336539 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334710, d336539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334710, d336539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334711 q = 0) : d336540 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d334711, d336540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334711, d336540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro34978 (p : Pattern) (selected : d334714 p = 0) : d336543 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334692 q = 0) : d336521 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334692, d336521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34973 q selected
    | true =>
      simp only [d334692, d336521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334693 q = 0) : d336522 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334693, d336522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334693, d336522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334696 q = 0) : d336525 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334696, d336525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34974 q selected
    | true =>
      simp only [d334696, d336525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334697 q = 0) : d336526 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334697, d336526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334697, d336526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334698 q = 0) : d336527 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334698, d336527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334698, d336527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334699 q = 0) : d336528 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334699, d336528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334699, d336528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334700 q = 0) : d336529 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334700, d336529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334700, d336529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334714 q = 0) : d336543 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334714, d336543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334714, d336543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro34979 (p : Pattern) (selected : d334715 p = 0) : d336544 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334696 q = 0) : d336525 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334696, d336525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34974 q selected
    | true =>
      simp only [d334696, d336525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334697 q = 0) : d336526 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334697, d336526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334697, d336526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334702 q = 0) : d336531 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334702, d336531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334702, d336531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334703 q = 0) : d336532 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334703, d336532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334703, d336532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334704 q = 0) : d336533 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334704, d336533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334704, d336533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334715 q = 0) : d336544 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334715, d336544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334715, d336544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34980 (p : Pattern) (selected : d334721 p = 0) : d336550 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334706 q = 0) : d336535 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334706, d336535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34975 q selected
    | true =>
      simp only [d334706, d336535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34976 q selected
  have h2 (q : Pattern) (selected : d334707 q = 0) : d336536 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334707, d336536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334707, d336536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334708 q = 0) : d336537 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334708, d336537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334708, d336537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334709 q = 0) : d336538 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334709, d336538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334709, d336538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334710 q = 0) : d336539 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334710, d336539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334710, d336539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334716 q = 0) : d336545 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d334716, d336545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34978 q selected
    | true =>
      simp only [d334716, d336545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34979 q selected
  have h7 (q : Pattern) (selected : d334717 q = 0) : d336546 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d334717, d336546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334717, d336546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334718 q = 0) : d336547 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d334718, d336547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334718, d336547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334719 q = 0) : d336548 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d334719, d336548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334719, d336548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334720 q = 0) : d336549 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d334720, d336549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334720, d336549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d334721 q = 0) : d336550 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d334721, d336550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334721, d336550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro34981 (p : Pattern) (selected : d334726 p = 0) : d336555 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334692 q = 0) : d336521 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334692, d336521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34973 q selected
    | true =>
      simp only [d334692, d336521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334693 q = 0) : d336522 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334693, d336522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334693, d336522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334696 q = 0) : d336525 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334696, d336525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34974 q selected
    | true =>
      simp only [d334696, d336525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334697 q = 0) : d336526 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334697, d336526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334697, d336526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334698 q = 0) : d336527 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334698, d336527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334698, d336527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334699 q = 0) : d336528 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334699, d336528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334699, d336528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334725 q = 0) : d336554 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334725, d336554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334725, d336554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334726 q = 0) : d336555 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334726, d336555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334726, d336555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro34982 (p : Pattern) (selected : d334728 p = 0) : d336557 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334696 q = 0) : d336525 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334696, d336525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34974 q selected
    | true =>
      simp only [d334696, d336525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334697 q = 0) : d336526 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334697, d336526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334697, d336526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334702 q = 0) : d336531 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334702, d336531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334702, d336531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334703 q = 0) : d336532 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334703, d336532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334703, d336532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334727 q = 0) : d336556 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334727, d336556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334727, d336556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334728 q = 0) : d336557 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334728, d336557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334728, d336557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro34983 (p : Pattern) (selected : d334735 p = 0) : d336564 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334692 q = 0) : d336521 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334692, d336521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34973 q selected
    | true =>
      simp only [d334692, d336521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334693 q = 0) : d336522 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334693, d336522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334693, d336522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334696 q = 0) : d336525 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334696, d336525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34974 q selected
    | true =>
      simp only [d334696, d336525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334697 q = 0) : d336526 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334697, d336526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334697, d336526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334698 q = 0) : d336527 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334698, d336527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334698, d336527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334733 q = 0) : d336562 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334733, d336562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334733, d336562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334734 q = 0) : d336563 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334734, d336563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334734, d336563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334735 q = 0) : d336564 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334735, d336564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334735, d336564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro34984 (p : Pattern) (selected : d334738 p = 0) : d336567 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334696 q = 0) : d336525 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334696, d336525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34974 q selected
    | true =>
      simp only [d334696, d336525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334697 q = 0) : d336526 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334697, d336526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334697, d336526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334702 q = 0) : d336531 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334702, d336531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334702, d336531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334736 q = 0) : d336565 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334736, d336565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334736, d336565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334737 q = 0) : d336566 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334737, d336566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334737, d336566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334738 q = 0) : d336567 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334738, d336567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334738, d336567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro34985 (p : Pattern) (selected : d334745 p = 0) : d336574 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334652 q = 0) : d336481 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334652, d336481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34966 q selected
    | true =>
      simp only [d334652, d336481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334653 q = 0) : d336482 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334653, d336482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334653, d336482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334654 q = 0) : d336483 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334654, d336483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334654, d336483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334655 q = 0) : d336484 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334655, d336484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334655, d336484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334656 q = 0) : d336485 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334656, d336485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334656, d336485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334672 q = 0) : d336501 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334672, d336501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334672, d336501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334745 q = 0) : d336574 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334745, d336574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334745, d336574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro34986 (p : Pattern) (selected : d334751 p = 0) : d336580 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334742 q = 0) : d336571 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334742, d336571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334742, d336571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34967 q selected
  have h2 (q : Pattern) (selected : d334743 q = 0) : d336572 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334743, d336572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334743, d336572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334744 q = 0) : d336573 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334744, d336573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334744, d336573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334746 q = 0) : d336575 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334746, d336575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34967 q selected
    | true =>
      simp only [d334746, d336575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34985 q selected
  have h5 (q : Pattern) (selected : d334747 q = 0) : d336576 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334747, d336576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334747, d336576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334748 q = 0) : d336577 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334748, d336577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334748, d336577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334749 q = 0) : d336578 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334749, d336578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334749, d336578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334674 q = 0) : d336503 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334674, d336503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34967 q selected
    | true =>
      simp only [d334674, d336503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34970 q selected
  have h9 (q : Pattern) (selected : d334675 q = 0) : d336504 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334675, d336504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334675, d336504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334676 q = 0) : d336505 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334676, d336505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334676, d336505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d334685 q = 0) : d336514 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334685, d336514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34970 q selected
    | true =>
      simp only [d334685, d336514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34972 q selected
  have h12 (q : Pattern) (selected : d334686 q = 0) : d336515 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334686, d336515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334686, d336515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d334687 q = 0) : d336516 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334687, d336516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334687, d336516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d334688 q = 0) : d336517 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334688, d336517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d334688, d336517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d334750 q = 0) : d336579 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334750, d336579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334750, d336579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d334751 q = 0) : d336580 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334751, d336580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d334751, d336580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro34987 (p : Pattern) (selected : d334757 p = 0) : d336586 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334752 q = 0) : d336581 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334752, d336581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34986 q selected
    | true =>
      simp only [d334752, d336581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334753 q = 0) : d336582 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334753, d336582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334753, d336582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334692 q = 0) : d336521 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334692, d336521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34973 q selected
    | true =>
      simp only [d334692, d336521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334693 q = 0) : d336522 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334693, d336522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334693, d336522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334754 q = 0) : d336583 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334754, d336583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334754, d336583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334755 q = 0) : d336584 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334755, d336584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334755, d336584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334756 q = 0) : d336585 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334756, d336585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334756, d336585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334757 q = 0) : d336586 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334757, d336586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334757, d336586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro34988 (p : Pattern) (selected : d334762 p = 0) : d336462 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334759 q = 0) : d336459 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334759, d336459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro498 q selected
    | true =>
      simp only [d334759, d336459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334760 q = 0) : d336460 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334760, d336460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334760, d336460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334761 q = 0) : d336461 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334761, d336461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334761, d336461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334762 q = 0) : d336462 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d334762, d336462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334762, d336462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h4 p selected
theorem eqIntro34989 (p : Pattern) (selected : d334769 p = 0) : d336469 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334354 q = 0) : d336000 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334354, d336000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23581 q selected
    | true =>
      simp only [d334354, d336000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334759 q = 0) : d336459 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334759, d336459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro498 q selected
    | true =>
      simp only [d334759, d336459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334767 q = 0) : d336467 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334767, d336467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334767, d336467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334768 q = 0) : d336468 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334768, d336468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334768, d336468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334769 q = 0) : d336469 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d334769, d336469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334769, d336469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro34990 (p : Pattern) (selected : d334780 p = 0) : d336480 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334759 q = 0) : d336459 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334759, d336459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro498 q selected
    | true =>
      simp only [d334759, d336459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334775 q = 0) : d336475 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334775, d336475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334775, d336475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334776 q = 0) : d336476 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334776, d336476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334776, d336476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334777 q = 0) : d336477 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334777, d336477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro500 q selected
    | true =>
      simp only [d334777, d336477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
  have h5 (q : Pattern) (selected : d334778 q = 0) : d336478 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334778, d336478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334778, d336478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334779 q = 0) : d336479 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334779, d336479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334779, d336479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334780 q = 0) : d336480 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d334780, d336480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334780, d336480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro34991 (p : Pattern) (selected : d334786 p = 0) : d336486 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334763 q = 0) : d336463 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334763, d336463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34988 q selected
    | true =>
      simp only [d334763, d336463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334764 q = 0) : d336464 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334764, d336464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334764, d336464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334765 q = 0) : d336465 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334765, d336465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334765, d336465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334766 q = 0) : d336466 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334766, d336466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334766, d336466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334770 q = 0) : d336470 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334770, d336470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34989 q selected
    | true =>
      simp only [d334770, d336470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334771 q = 0) : d336471 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334771, d336471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334771, d336471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334772 q = 0) : d336472 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334772, d336472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334772, d336472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334773 q = 0) : d336473 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334773, d336473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334773, d336473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334774 q = 0) : d336474 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334774, d336474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334774, d336474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334781 q = 0) : d336481 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334781, d336481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34990 q selected
    | true =>
      simp only [d334781, d336481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d334782 q = 0) : d336482 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334782, d336482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d334782, d336482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d334783 q = 0) : d336483 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334783, d336483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334783, d336483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d334784 q = 0) : d336484 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334784, d336484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d334784, d336484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d334785 q = 0) : d336485 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334785, d336485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334785, d336485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d334786 q = 0) : d336486 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334786, d336486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334786, d336486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro34992 (p : Pattern) (selected : d334790 p = 0) : d336490 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334354 q = 0) : d336000 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334354, d336000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23581 q selected
    | true =>
      simp only [d334354, d336000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334759 q = 0) : d336459 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334759, d336459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro498 q selected
    | true =>
      simp only [d334759, d336459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334767 q = 0) : d336467 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334767, d336467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334767, d336467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334768 q = 0) : d336468 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334768, d336468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334768, d336468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334787 q = 0) : d336487 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334787, d336487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro501 q selected
    | true =>
      simp only [d334787, d336487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334788 q = 0) : d336488 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334788, d336488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334788, d336488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334789 q = 0) : d336489 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334789, d336489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334789, d336489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334790 q = 0) : d336490 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d334790, d336490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334790, d336490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro34993 (p : Pattern) (selected : d334795 p = 0) : d336495 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334759 q = 0) : d336459 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334759, d336459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro498 q selected
    | true =>
      simp only [d334759, d336459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334787 q = 0) : d336487 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334787, d336487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro501 q selected
    | true =>
      simp only [d334787, d336487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334788 q = 0) : d336488 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334788, d336488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334788, d336488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334789 q = 0) : d336489 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334789, d336489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334789, d336489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334777 q = 0) : d336477 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334777, d336477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro500 q selected
    | true =>
      simp only [d334777, d336477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
  have h6 (q : Pattern) (selected : d334778 q = 0) : d336478 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334778, d336478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334778, d336478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334779 q = 0) : d336479 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334779, d336479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334779, d336479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334795 q = 0) : d336495 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d334795, d336495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334795, d336495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro34994 (p : Pattern) (selected : d334802 p = 0) : d336502 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334791 q = 0) : d336491 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334791, d336491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34992 q selected
    | true =>
      simp only [d334791, d336491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334792 q = 0) : d336492 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334792, d336492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334792, d336492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334793 q = 0) : d336493 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334793, d336493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334793, d336493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334794 q = 0) : d336494 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334794, d336494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334794, d336494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334796 q = 0) : d336496 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334796, d336496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34993 q selected
    | true =>
      simp only [d334796, d336496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334797 q = 0) : d336497 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334797, d336497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334797, d336497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334798 q = 0) : d336498 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334798, d336498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334798, d336498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334799 q = 0) : d336499 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334799, d336499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334799, d336499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334800 q = 0) : d336500 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334800, d336500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334800, d336500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334781 q = 0) : d336481 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334781, d336481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34990 q selected
    | true =>
      simp only [d334781, d336481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d334782 q = 0) : d336482 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334782, d336482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d334782, d336482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d334783 q = 0) : d336483 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334783, d336483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334783, d336483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d334784 q = 0) : d336484 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334784, d336484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d334784, d336484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d334801 q = 0) : d336501 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334801, d336501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d334801, d336501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d334802 q = 0) : d336502 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334802, d336502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334802, d336502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro34995 (p : Pattern) (selected : d334807 p = 0) : d336507 p = 1 := by
  have h0 (q : Pattern) (selected : d334777 q = 0) : d336477 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d334777, d336477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro500 q selected
    | true =>
      simp only [d334777, d336477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro209 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d334778 q = 0) : d336478 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d334778, d336478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334778, d336478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334779 q = 0) : d336479 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d334779, d336479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334779, d336479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d334807 q = 0) : d336507 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d334807, d336507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334807, d336507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h4 p selected
theorem eqIntro34996 (p : Pattern) (selected : d334813 p = 0) : d336513 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334796 q = 0) : d336496 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334796, d336496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34993 q selected
    | true =>
      simp only [d334796, d336496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334797 q = 0) : d336497 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334797, d336497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d334797, d336497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d334798 q = 0) : d336498 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334798, d336498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334798, d336498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334799 q = 0) : d336499 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334799, d336499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334799, d336499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334806 q = 0) : d336506 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334806, d336506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334806, d336506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334808 q = 0) : d336508 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d334808, d336508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34995 q selected
    | true =>
      simp only [d334808, d336508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334809 q = 0) : d336509 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d334809, d336509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334809, d336509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334810 q = 0) : d336510 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d334810, d336510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334810, d336510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d334811 q = 0) : d336511 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d334811, d336511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d334811, d336511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d334812 q = 0) : d336512 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d334812, d336512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334812, d336512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d334813 q = 0) : d336513 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d334813, d336513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334813, d336513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro34997 (p : Pattern) (selected : d334820 p = 0) : d336520 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334803 q = 0) : d336503 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334803, d336503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34991 q selected
    | true =>
      simp only [d334803, d336503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34994 q selected
  have h2 (q : Pattern) (selected : d334804 q = 0) : d336504 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334804, d336504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334804, d336504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334805 q = 0) : d336505 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334805, d336505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334805, d336505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334814 q = 0) : d336514 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334814, d336514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34994 q selected
    | true =>
      simp only [d334814, d336514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34996 q selected
  have h5 (q : Pattern) (selected : d334815 q = 0) : d336515 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334815, d336515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334815, d336515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334816 q = 0) : d336516 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334816, d336516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334816, d336516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d334817 q = 0) : d336517 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334817, d336517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334817, d336517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d334818 q = 0) : d336518 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334818, d336518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334818, d336518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d334819 q = 0) : d336519 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334819, d336519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d334819, d336519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d334820 q = 0) : d336520 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334820, d336520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d334820, d336520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro34998 (p : Pattern) (selected : d334824 p = 0) : d336524 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334814 q = 0) : d336514 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d334814, d336514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34994 q selected
    | true =>
      simp only [d334814, d336514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34996 q selected
  have h2 (q : Pattern) (selected : d334815 q = 0) : d336515 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d334815, d336515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334815, d336515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334816 q = 0) : d336516 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d334816, d336516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334816, d336516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d334818 q = 0) : d336518 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d334818, d336518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d334818, d336518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d334823 q = 0) : d336523 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d334823, d336523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d334823, d336523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d334824 q = 0) : d336524 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d334824, d336524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334824, d336524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro34999 (p : Pattern) (selected : d334830 p = 0) : d336530 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d334821 q = 0) : d336521 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334821, d336521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34997 q selected
    | true =>
      simp only [d334821, d336521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d334822 q = 0) : d336522 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334822, d336522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334822, d336522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d334825 q = 0) : d336525 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d334825, d336525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34998 q selected
    | true =>
      simp only [d334825, d336525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d334826 q = 0) : d336526 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d334826, d336526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334826, d336526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d334827 q = 0) : d336527 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d334827, d336527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d334827, d336527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334828 q = 0) : d336528 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334828, d336528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334828, d336528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d334829 q = 0) : d336529 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d334829, d336529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d334829, d336529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d334830 q = 0) : d336530 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d334830, d336530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d334830, d336530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
end NetHack.Soko22Hazard87
