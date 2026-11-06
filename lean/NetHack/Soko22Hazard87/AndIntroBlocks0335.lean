import NetHack.Soko22Hazard87.AndIntroBlocks0334
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro83750 (p : Pattern) (ha : d315357 p = 1) (hb : d316666 p = 1) : d317581 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315329 q = 1) (hb : d316638 q = 1) : d317553 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315329, d316638, d317553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83745 q ha hb
    | true =>
      simp only [d315329, d316638, d317553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83727 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d315251 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d315330 q = 1) (hb : d316639 q = 1) : d317554 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315330, d316639, d317554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d315330, d316639, d317554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d315332 q = 1) (hb : d316641 q = 1) : d317556 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315332, d316641, d317556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83746 q ha hb
    | true =>
      simp only [d315332, d316641, d317556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d315333 q = 1) (hb : d316642 q = 1) : d317557 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315333, d316642, d317557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315333, d316642, d317557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d315334 q = 1) (hb : d316643 q = 1) : d317558 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315334, d316643, d317558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315334, d316643, d317558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d315355 q = 1) (hb : d316664 q = 1) : d317579 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315355, d316664, d317579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315355, d316664, d317579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d315356 q = 1) (hb : d316665 q = 1) : d317580 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d315356, d316665, d317580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315356, d316665, d317580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d315357 q = 1) (hb : d316666 q = 1) : d317581 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d315357, d316666, d317581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315357, d316666, d317581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro83751 (p : Pattern) (ha : d315359 p = 1) (hb : d316668 p = 1) : d317583 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315345 q = 1) (hb : d316654 q = 1) : d317569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315345, d316654, d317569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83728 q ha hb
    | true =>
      simp only [d315345, d316654, d317569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315346 q = 1) (hb : d316655 q = 1) : d317570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315346, d316655, d317570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315346, d316655, d317570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315347 q = 1) (hb : d316656 q = 1) : d317571 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315347, d316656, d317571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315347, d316656, d317571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315348 q = 1) (hb : d316657 q = 1) : d317572 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315348, d316657, d317572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315348, d316657, d317572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315349 q = 1) (hb : d316658 q = 1) : d317573 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d315349, d316658, d317573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315349, d316658, d317573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315359 q = 1) (hb : d316668 q = 1) : d317583 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d315359, d316668, d317583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315359, d316668, d317583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83752 (p : Pattern) (ha : d286547 p = 1) (hb : d315415 p = 1) : d317627 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d286527 q = 1) (hb : d315400 q = 1) : d317617 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d286527, d315400, d317617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d286527, d315400, d317617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83714 q ha hb
  have h2 (q : Pattern) (ha : d286343 q = 1) (hb : d315202 q = 1) : d317444 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d286343, d315202, d317444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83714 q ha hb
    | true =>
      simp only [d286343, d315202, d317444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d286528 q = 1) (hb : d315401 q = 1) : d317618 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d286528, d315401, d317618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286528, d315401, d317618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d286344 q = 1) (hb : d315203 q = 1) : d317445 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d286344, d315203, d317445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d286344, d315203, d317445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d286529 q = 1) (hb : d315402 q = 1) : d317619 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d286529, d315402, d317619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d286529, d315402, d317619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d286530 q = 1) (hb : d315403 q = 1) : d317620 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d286530, d315403, d317620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d286530, d315403, d317620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d286536 q = 1) (hb : d315409 q = 1) : d317626 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d286536, d315409, d317626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d286536, d315409, d317626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d315414 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d286547 q = 1) (hb : d315415 q = 1) : d317627 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d286547, d315415, d317627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d286547, d315415, d317627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro83753 (p : Pattern) (ha : d315385 p = 1) (hb : d316690 p = 1) : d317603 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315371 q = 1) (hb : d316443 q = 1) : d317589 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315371, d316443, d317589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315371, d316443, d317589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83717 q ha hb
  have h2 (q : Pattern) (ha : d315164 q = 1) (hb : d316358 q = 1) : d317415 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315164, d316358, d317415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83717 q ha hb
    | true =>
      simp only [d315164, d316358, d317415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d315372 q = 1) (hb : d316444 q = 1) : d317590 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315372, d316444, d317590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d315372, d316444, d317590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315165 q = 1) (hb : d316359 q = 1) : d317416 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315165, d316359, d317416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315165, d316359, d317416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d315373 q = 1) (hb : d316445 q = 1) : d317591 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d315373, d316445, d317591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315373, d316445, d317591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315374 q = 1) (hb : d316446 q = 1) : d317592 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d315374, d316446, d317592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315374, d316446, d317592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d315375 q = 1) (hb : d316447 q = 1) : d317593 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315375, d316447, d317593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315375, d316447, d317593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83718 q ha hb
  have h8 (q : Pattern) (ha : d315172 q = 1) (hb : d316368 q = 1) : d317420 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315172, d316368, d317420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83718 q ha hb
    | true =>
      simp only [d315172, d316368, d317420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d315376 q = 1) (hb : d316448 q = 1) : d317594 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315376, d316448, d317594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d315376, d316448, d317594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d315173 q = 1) (hb : d316369 q = 1) : d317421 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315173, d316369, d317421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d315173, d316369, d317421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d315377 q = 1) (hb : d316449 q = 1) : d317595 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d315377, d316449, d317595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d315377, d316449, d317595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d315378 q = 1) (hb : d316450 q = 1) : d317596 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d315378, d316450, d317596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d315378, d316450, d317596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d315379 q = 1) (hb : d316451 q = 1) : d317597 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d315379, d316451, d317597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315379, d316451, d317597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d315368 q = 1) (hb : d316455 q = 1) : d316455 q = 1 := by
    exact hb
  have h15 (q : Pattern) (ha : d286527 q = 1) (hb : d315380 q = 1) : d317598 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d286527, d315380, d317598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d286527, d315380, d317598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83716 q ha hb
  have h16 (q : Pattern) (ha : d286343 q = 1) (hb : d315187 q = 1) : d317429 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d286343, d315187, d317429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83716 q ha hb
    | true =>
      simp only [d286343, d315187, d317429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d286528 q = 1) (hb : d315381 q = 1) : d317599 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d286528, d315381, d317599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d286528, d315381, d317599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d286344 q = 1) (hb : d315188 q = 1) : d317430 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d286344, d315188, d317430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d286344, d315188, d317430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d286529 q = 1) (hb : d315382 q = 1) : d317600 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d286529, d315382, d317600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d286529, d315382, d317600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d286530 q = 1) (hb : d315383 q = 1) : d317601 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d286530, d315383, d317601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d286530, d315383, d317601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d315384 q = 1) (hb : d316689 q = 1) : d317602 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d315384, d316689, d317602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d315384, d316689, d317602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
  have h22 (q : Pattern) (ha : d315385 q = 1) (hb : d316690 q = 1) : d317603 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d315385, d316690, d317603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d315385, d316690, d317603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro83754 (p : Pattern) (ha : d315391 p = 1) (hb : d316694 p = 1) : d317608 p = 1 := by
  have h0 (q : Pattern) (ha : d315378 q = 1) (hb : d316455 q = 1) : d316455 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d286527 q = 1) (hb : d315380 q = 1) : d317598 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d286527, d315380, d317598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286527, d315380, d317598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83716 q ha hb
  have h3 (q : Pattern) (ha : d286343 q = 1) (hb : d315187 q = 1) : d317429 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d286343, d315187, d317429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83716 q ha hb
    | true =>
      simp only [d286343, d315187, d317429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d286528 q = 1) (hb : d315381 q = 1) : d317599 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d286528, d315381, d317599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d286528, d315381, d317599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d286344 q = 1) (hb : d315188 q = 1) : d317430 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d286344, d315188, d317430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d286344, d315188, d317430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d286529 q = 1) (hb : d315382 q = 1) : d317600 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d286529, d315382, d317600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d286529, d315382, d317600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d286530 q = 1) (hb : d315383 q = 1) : d317601 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d286530, d315383, d317601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d286530, d315383, d317601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d315389 q = 1) (hb : d316689 q = 1) : d317602 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d315389, d316689, d317602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d315389, d316689, d317602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d286536 q = 1) (hb : d315390 q = 1) : d317607 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d286536, d315390, d317607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d286536, d315390, d317607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d315391 q = 1) (hb : d316694 q = 1) : d317608 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d315391, d316694, d317608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d315391, d316694, d317608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro83755 (p : Pattern) (ha : d315405 p = 1) (hb : d316700 p = 1) : d317622 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315396 q = 1) (hb : d316278 q = 1) : d317613 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315396, d316278, d317613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315396, d316278, d317613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83720 q ha hb
  have h2 (q : Pattern) (ha : d315197 q = 1) (hb : d316235 q = 1) : d317439 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315197, d316235, d317439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83720 q ha hb
    | true =>
      simp only [d315197, d316235, d317439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d315397 q = 1) (hb : d316279 q = 1) : d317614 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315397, d316279, d317614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d315397, d316279, d317614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315198 q = 1) (hb : d316236 q = 1) : d317440 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315198, d316236, d317440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315198, d316236, d317440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d315398 q = 1) (hb : d316280 q = 1) : d317615 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d315398, d316280, d317615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315398, d316280, d317615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315399 q = 1) (hb : d316281 q = 1) : d317616 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d315399, d316281, d317616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315399, d316281, d317616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d286527 q = 1) (hb : d315400 q = 1) : d317617 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d286527, d315400, d317617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d286527, d315400, d317617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83714 q ha hb
  have h8 (q : Pattern) (ha : d286343 q = 1) (hb : d315202 q = 1) : d317444 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d286343, d315202, d317444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83714 q ha hb
    | true =>
      simp only [d286343, d315202, d317444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d286528 q = 1) (hb : d315401 q = 1) : d317618 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d286528, d315401, d317618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d286528, d315401, d317618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d286344 q = 1) (hb : d315203 q = 1) : d317445 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d286344, d315203, d317445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d286344, d315203, d317445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d286529 q = 1) (hb : d315402 q = 1) : d317619 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d286529, d315402, d317619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d286529, d315402, d317619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d286530 q = 1) (hb : d315403 q = 1) : d317620 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d286530, d315403, d317620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d286530, d315403, d317620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d315404 q = 1) (hb : d316699 q = 1) : d317621 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d315404, d316699, d317621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315404, d316699, d317621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d286527 q = 1) (hb : d315380 q = 1) : d317598 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d286527, d315380, d317598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d286527, d315380, d317598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83716 q ha hb
  have h15 (q : Pattern) (ha : d286343 q = 1) (hb : d315187 q = 1) : d317429 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d286343, d315187, d317429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83716 q ha hb
    | true =>
      simp only [d286343, d315187, d317429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d286528 q = 1) (hb : d315381 q = 1) : d317599 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d286528, d315381, d317599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d286528, d315381, d317599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d286344 q = 1) (hb : d315188 q = 1) : d317430 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d286344, d315188, d317430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d286344, d315188, d317430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d286529 q = 1) (hb : d315382 q = 1) : d317600 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d286529, d315382, d317600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d286529, d315382, d317600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d286530 q = 1) (hb : d315383 q = 1) : d317601 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d286530, d315383, d317601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d286530, d315383, d317601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d286536 q = 1) (hb : d315390 q = 1) : d317607 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d286536, d315390, d317607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d286536, d315390, d317607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d315405 q = 1) (hb : d316700 q = 1) : d317622 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d315405, d316700, d317622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d315405, d316700, d317622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
  exact h21 p ha hb
theorem andIntro83756 (p : Pattern) (ha : d315421 p = 1) (hb : d316709 p = 1) : d317633 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315370 q = 1) (hb : d316688 q = 1) : d316688 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d315386 q = 1) (hb : d316691 q = 1) : d317604 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315386, d316691, d317604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d315386, d316691, d317604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83753 q ha hb
  have h3 (q : Pattern) (ha : d315387 q = 1) (hb : d316692 q = 1) : d317605 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315387, d316692, d317605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315387, d316692, d317605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315388 q = 1) (hb : d316693 q = 1) : d317606 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315388, d316693, d317606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315388, d316693, d317606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315392 q = 1) (hb : d316695 q = 1) : d317609 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315392, d316695, d317609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83753 q ha hb
    | true =>
      simp only [d315392, d316695, d317609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83754 q ha hb
  have h6 (q : Pattern) (ha : d315393 q = 1) (hb : d316696 q = 1) : d317610 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315393, d316696, d317610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315393, d316696, d317610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d315394 q = 1) (hb : d316697 q = 1) : d317611 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315394, d316697, d317611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315394, d316697, d317611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d315395 q = 1) (hb : d316698 q = 1) : d317612 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d315395, d316698, d317612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315395, d316698, d317612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d315406 q = 1) (hb : d316701 q = 1) : d317623 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315406, d316701, d317623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83753 q ha hb
    | true =>
      simp only [d315406, d316701, d317623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83755 q ha hb
  have h10 (q : Pattern) (ha : d315407 q = 1) (hb : d316702 q = 1) : d317624 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315407, d316702, d317624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315407, d316702, d317624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d315408 q = 1) (hb : d316703 q = 1) : d317625 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315408, d316703, d317625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315408, d316703, d317625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d315416 q = 1) (hb : d316704 q = 1) : d317628 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315416, d316704, d317628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83755 q ha hb
    | true =>
      simp only [d315416, d316704, d317628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83752 q hb ha
  have h13 (q : Pattern) (ha : d315417 q = 1) (hb : d316705 q = 1) : d317629 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315417, d316705, d317629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315417, d316705, d317629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d315418 q = 1) (hb : d316706 q = 1) : d317630 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315418, d316706, d317630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315418, d316706, d317630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d315419 q = 1) (hb : d316707 q = 1) : d317631 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d315419, d316707, d317631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d315419, d316707, d317631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d315420 q = 1) (hb : d316708 q = 1) : d317632 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d315420, d316708, d317632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d315420, d316708, d317632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d315421 q = 1) (hb : d316709 q = 1) : d317633 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d315421, d316709, d317633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d315421, d316709, d317633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h17 p ha hb
theorem andIntro83757 (p : Pattern) (ha : d315426 p = 1) (hb : d316714 p = 1) : d317638 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315406 q = 1) (hb : d316701 q = 1) : d317623 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315406, d316701, d317623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83753 q ha hb
    | true =>
      simp only [d315406, d316701, d317623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83755 q ha hb
  have h2 (q : Pattern) (ha : d315407 q = 1) (hb : d316702 q = 1) : d317624 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315407, d316702, d317624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315407, d316702, d317624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315408 q = 1) (hb : d316703 q = 1) : d317625 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315408, d316703, d317625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315408, d316703, d317625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315416 q = 1) (hb : d316704 q = 1) : d317628 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315416, d316704, d317628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83755 q ha hb
    | true =>
      simp only [d315416, d316704, d317628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83752 q hb ha
  have h5 (q : Pattern) (ha : d315417 q = 1) (hb : d316705 q = 1) : d317629 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315417, d316705, d317629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315417, d316705, d317629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315418 q = 1) (hb : d316706 q = 1) : d317630 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315418, d316706, d317630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315418, d316706, d317630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d315419 q = 1) (hb : d316707 q = 1) : d317631 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d315419, d316707, d317631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315419, d316707, d317631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d315424 q = 1) (hb : d316712 q = 1) : d317636 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d315424, d316712, d317636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315424, d316712, d317636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d315425 q = 1) (hb : d316713 q = 1) : d317637 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d315425, d316713, d317637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d315425, d316713, d317637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d315426 q = 1) (hb : d316714 q = 1) : d317638 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d315426, d316714, d317638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d315426, d316714, d317638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro83758 (p : Pattern) (ha : d315432 p = 1) (hb : d316720 p = 1) : d317644 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315422 q = 1) (hb : d316710 q = 1) : d317634 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315422, d316710, d317634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83756 q ha hb
    | true =>
      simp only [d315422, d316710, d317634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315423 q = 1) (hb : d316711 q = 1) : d317635 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315423, d316711, d317635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315423, d316711, d317635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315427 q = 1) (hb : d316715 q = 1) : d317639 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315427, d316715, d317639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83757 q ha hb
    | true =>
      simp only [d315427, d316715, d317639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315428 q = 1) (hb : d316716 q = 1) : d317640 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315428, d316716, d317640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315428, d316716, d317640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315429 q = 1) (hb : d316717 q = 1) : d317641 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315429, d316717, d317641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315429, d316717, d317641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315430 q = 1) (hb : d316718 q = 1) : d317642 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315430, d316718, d317642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315430, d316718, d317642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d315431 q = 1) (hb : d316719 q = 1) : d317643 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315431, d316719, d317643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315431, d316719, d317643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d315432 q = 1) (hb : d316720 q = 1) : d317644 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315432, d316720, d317644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d315432, d316720, d317644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro83759 (p : Pattern) (ha : d315434 p = 1) (hb : d316722 p = 1) : d317646 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315416 q = 1) (hb : d316704 q = 1) : d317628 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315416, d316704, d317628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83755 q ha hb
    | true =>
      simp only [d315416, d316704, d317628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83752 q hb ha
  have h2 (q : Pattern) (ha : d315417 q = 1) (hb : d316705 q = 1) : d317629 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315417, d316705, d317629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315417, d316705, d317629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315418 q = 1) (hb : d316706 q = 1) : d317630 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315418, d316706, d317630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315418, d316706, d317630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315424 q = 1) (hb : d316712 q = 1) : d317636 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d315424, d316712, d317636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315424, d316712, d317636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d315433 q = 1) (hb : d316721 q = 1) : d317645 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d315433, d316721, d317645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315433, d316721, d317645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d315434 q = 1) (hb : d316722 q = 1) : d317646 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d315434, d316722, d317646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315434, d316722, d317646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83760 (p : Pattern) (ha : d315440 p = 1) (hb : d316728 p = 1) : d317652 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315427 q = 1) (hb : d316715 q = 1) : d317639 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315427, d316715, d317639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83757 q ha hb
    | true =>
      simp only [d315427, d316715, d317639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315428 q = 1) (hb : d316716 q = 1) : d317640 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315428, d316716, d317640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315428, d316716, d317640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315435 q = 1) (hb : d316723 q = 1) : d317647 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315435, d316723, d317647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83759 q ha hb
    | true =>
      simp only [d315435, d316723, d317647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315436 q = 1) (hb : d316724 q = 1) : d317648 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315436, d316724, d317648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315436, d316724, d317648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315437 q = 1) (hb : d316725 q = 1) : d317649 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315437, d316725, d317649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315437, d316725, d317649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315438 q = 1) (hb : d316726 q = 1) : d317650 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315438, d316726, d317650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315438, d316726, d317650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d315439 q = 1) (hb : d316727 q = 1) : d317651 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315439, d316727, d317651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315439, d316727, d317651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d315440 q = 1) (hb : d316728 q = 1) : d317652 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315440, d316728, d317652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d315440, d316728, d317652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro83761 (p : Pattern) (ha : d286547 p = 1) (hb : d315448 p = 1) : d317627 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d286527 q = 1) (hb : d315400 q = 1) : d317617 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d286527, d315400, d317617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d286527, d315400, d317617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83714 q ha hb
  have h2 (q : Pattern) (ha : d286343 q = 1) (hb : d315202 q = 1) : d317444 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d286343, d315202, d317444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83714 q ha hb
    | true =>
      simp only [d286343, d315202, d317444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d286528 q = 1) (hb : d315401 q = 1) : d317618 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d286528, d315401, d317618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286528, d315401, d317618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d286344 q = 1) (hb : d315203 q = 1) : d317445 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d286344, d315203, d317445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d286344, d315203, d317445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d286529 q = 1) (hb : d315402 q = 1) : d317619 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d286529, d315402, d317619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d286529, d315402, d317619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d286530 q = 1) (hb : d315403 q = 1) : d317620 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d286530, d315403, d317620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d286530, d315403, d317620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d286536 q = 1) (hb : d315409 q = 1) : d317626 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d286536, d315409, d317626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d286536, d315409, d317626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d286547 q = 1) (hb : d315448 q = 1) : d317627 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d286547, d315448, d317627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d286547, d315448, d317627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro83762 (p : Pattern) (ha : d315454 p = 1) (hb : d316714 p = 1) : d317638 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315406 q = 1) (hb : d316701 q = 1) : d317623 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315406, d316701, d317623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83753 q ha hb
    | true =>
      simp only [d315406, d316701, d317623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83755 q ha hb
  have h2 (q : Pattern) (ha : d315407 q = 1) (hb : d316702 q = 1) : d317624 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315407, d316702, d317624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315407, d316702, d317624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315408 q = 1) (hb : d316703 q = 1) : d317625 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315408, d316703, d317625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315408, d316703, d317625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315416 q = 1) (hb : d316704 q = 1) : d317628 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315416, d316704, d317628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83755 q ha hb
    | true =>
      simp only [d315416, d316704, d317628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83752 q hb ha
  have h5 (q : Pattern) (ha : d315417 q = 1) (hb : d316705 q = 1) : d317629 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315417, d316705, d317629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315417, d316705, d317629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315418 q = 1) (hb : d316706 q = 1) : d317630 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315418, d316706, d317630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315418, d316706, d317630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d315419 q = 1) (hb : d316707 q = 1) : d317631 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d315419, d316707, d317631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315419, d316707, d317631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d315449 q = 1) (hb : d316704 q = 1) : d317628 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315449, d316704, d317628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83755 q ha hb
    | true =>
      simp only [d315449, d316704, d317628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83761 q hb ha
  have h9 (q : Pattern) (ha : d315450 q = 1) (hb : d316705 q = 1) : d317629 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315450, d316705, d317629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315450, d316705, d317629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d315451 q = 1) (hb : d316706 q = 1) : d317630 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315451, d316706, d317630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315451, d316706, d317630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d315452 q = 1) (hb : d316712 q = 1) : d317636 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d315452, d316712, d317636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d315452, d316712, d317636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d315453 q = 1) (hb : d316713 q = 1) : d317637 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d315453, d316713, d317637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d315453, d316713, d317637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d315454 q = 1) (hb : d316714 q = 1) : d317638 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d315454, d316714, d317638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d315454, d316714, d317638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro83763 (p : Pattern) (ha : d315460 p = 1) (hb : d316734 p = 1) : d317658 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315455 q = 1) (hb : d316715 q = 1) : d317639 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315455, d316715, d317639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83762 q ha hb
    | true =>
      simp only [d315455, d316715, d317639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315456 q = 1) (hb : d316716 q = 1) : d317640 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315456, d316716, d317640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315456, d316716, d317640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315457 q = 1) (hb : d316731 q = 1) : d317655 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315457, d316731, d317655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315457, d316731, d317655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315458 q = 1) (hb : d316732 q = 1) : d317656 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315458, d316732, d317656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315458, d316732, d317656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d315459 q = 1) (hb : d316733 q = 1) : d317657 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315459, d316733, d317657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315459, d316733, d317657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d315460 q = 1) (hb : d316734 q = 1) : d317658 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315460, d316734, d317658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315460, d316734, d317658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83764 (p : Pattern) (ha : d315466 p = 1) (hb : d316740 p = 1) : d317664 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315441 q = 1) (hb : d316729 q = 1) : d317653 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315441, d316729, d317653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83758 q ha hb
    | true =>
      simp only [d315441, d316729, d317653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83760 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d315446 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d315447 q = 1) (hb : d316730 q = 1) : d317654 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315447, d316730, d317654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d315447, d316730, d317654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d315461 q = 1) (hb : d316735 q = 1) : d317659 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315461, d316735, d317659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83763 q ha hb
    | true =>
      simp only [d315461, d316735, d317659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d315462 q = 1) (hb : d316736 q = 1) : d317660 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315462, d316736, d317660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315462, d316736, d317660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d315463 q = 1) (hb : d316737 q = 1) : d317661 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315463, d316737, d317661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315463, d316737, d317661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d315464 q = 1) (hb : d316738 q = 1) : d317662 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315464, d316738, d317662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315464, d316738, d317662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d315465 q = 1) (hb : d316739 q = 1) : d317663 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d315465, d316739, d317663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315465, d316739, d317663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d315466 q = 1) (hb : d316740 q = 1) : d317664 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d315466, d316740, d317664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315466, d316740, d317664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro83765 (p : Pattern) (ha : d315445 p = 1) (hb : d316745 p = 1) : d317669 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315435 q = 1) (hb : d316723 q = 1) : d317647 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315435, d316723, d317647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83759 q ha hb
    | true =>
      simp only [d315435, d316723, d317647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315436 q = 1) (hb : d316724 q = 1) : d317648 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315436, d316724, d317648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315436, d316724, d317648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315442 q = 1) (hb : d316742 q = 1) : d317666 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315442, d316742, d317666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315442, d316742, d317666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315443 q = 1) (hb : d316743 q = 1) : d317667 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315443, d316743, d317667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315443, d316743, d317667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d315444 q = 1) (hb : d316744 q = 1) : d317668 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315444, d316744, d317668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315444, d316744, d317668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d315445 q = 1) (hb : d316745 q = 1) : d317669 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315445, d316745, d317669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315445, d316745, d317669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83766 (p : Pattern) (ha : d315473 p = 1) (hb : d316751 p = 1) : d317675 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315468 q = 1) (hb : d316746 q = 1) : d317670 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315468, d316746, d317670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83765 q ha hb
    | true =>
      simp only [d315468, d316746, d317670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315469 q = 1) (hb : d316747 q = 1) : d317671 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315469, d316747, d317671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315469, d316747, d317671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315470 q = 1) (hb : d316748 q = 1) : d317672 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315470, d316748, d317672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315470, d316748, d317672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315471 q = 1) (hb : d316749 q = 1) : d317673 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315471, d316749, d317673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315471, d316749, d317673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315472 q = 1) (hb : d316750 q = 1) : d317674 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d315472, d316750, d317674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315472, d316750, d317674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315473 q = 1) (hb : d316751 q = 1) : d317675 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d315473, d316751, d317675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315473, d316751, d317675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83767 (p : Pattern) (ha : d315479 p = 1) (hb : d316757 p = 1) : d317681 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315247 q = 1) (hb : d316541 q = 1) : d317483 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d315247, d316541, d317483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315247, d316541, d317483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83726 q ha hb
  have h2 (q : Pattern) (ha : d315248 q = 1) (hb : d316542 q = 1) : d317484 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d315248, d316542, d317484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d315248, d316542, d317484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d315257 q = 1) (hb : d316551 q = 1) : d317493 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d315257, d316551, d317493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83726 q ha hb
    | true =>
      simp only [d315257, d316551, d317493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83729 q ha hb
  have h4 (q : Pattern) (ha : d315258 q = 1) (hb : d316552 q = 1) : d317494 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d315258, d316552, d317494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315258, d316552, d317494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d315259 q = 1) (hb : d316553 q = 1) : d317495 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d315259, d316553, d317495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315259, d316553, d317495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315338 q = 1) (hb : d316647 q = 1) : d317562 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d315338, d316647, d317562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83740 q ha hb
    | true =>
      simp only [d315338, d316647, d317562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83747 q ha hb
  have h7 (q : Pattern) (ha : d315351 q = 1) (hb : d316660 q = 1) : d317575 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d315351, d316660, d317575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83748 q ha hb
    | true =>
      simp only [d315351, d316660, d317575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83749 q ha hb
  have h8 (q : Pattern) (ha : d315352 q = 1) (hb : d316661 q = 1) : d317576 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d315352, d316661, d317576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315352, d316661, d317576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d315353 q = 1) (hb : d316662 q = 1) : d317577 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d315353, d316662, d317577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d315353, d316662, d317577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d315354 q = 1) (hb : d316663 q = 1) : d317578 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d315354, d316663, d317578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315354, d316663, d317578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d315358 q = 1) (hb : d316667 q = 1) : d317582 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d315358, d316667, d317582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315358, d316667, d317582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83750 q ha hb
  have h12 (q : Pattern) (ha : d315360 q = 1) (hb : d316669 q = 1) : d317584 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d315360, d316669, d317584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315360, d316669, d317584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83751 q ha hb
  have h13 (q : Pattern) (ha : d315361 q = 1) (hb : d316670 q = 1) : d317585 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d315361, d316670, d317585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d315361, d316670, d317585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d315362 q = 1) (hb : d316671 q = 1) : d317586 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d315362, d316671, d317586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d315362, d316671, d317586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d315363 q = 1) (hb : d316672 q = 1) : d317587 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d315363, d316672, d317587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d315363, d316672, d317587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d315364 q = 1) (hb : d316673 q = 1) : d317588 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d315364, d316673, d317588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d315364, d316673, d317588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d315467 q = 1) (hb : d316741 q = 1) : d317665 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d315467, d316741, d317665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315467, d316741, d317665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83764 q ha hb
  have h18 (q : Pattern) (ha : d315474 q = 1) (hb : d316752 q = 1) : d317676 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d315474, d316752, d317676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315474, d316752, d317676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83766 q ha hb
  have h19 (q : Pattern) (ha : d315475 q = 1) (hb : d316753 q = 1) : d317677 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d315475, d316753, d317677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d315475, d316753, d317677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d315476 q = 1) (hb : d316754 q = 1) : d317678 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d315476, d316754, d317678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d315476, d316754, d317678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d315477 q = 1) (hb : d316755 q = 1) : d317679 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d315477, d316755, d317679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d315477, d316755, d317679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d315478 q = 1) (hb : d316756 q = 1) : d317680 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d315478, d316756, d317680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d315478, d316756, d317680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d315479 q = 1) (hb : d316757 q = 1) : d317681 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d315479, d316757, d317681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d315479, d316757, d317681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro83768 (p : Pattern) (ha : d315485 p = 1) (hb : d316763 p = 1) : d317687 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315480 q = 1) (hb : d316758 q = 1) : d317682 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d315480, d316758, d317682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315480, d316758, d317682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83767 q ha hb
  have h2 (q : Pattern) (ha : d315481 q = 1) (hb : d316759 q = 1) : d317683 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d315481, d316759, d317683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315481, d316759, d317683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315482 q = 1) (hb : d316760 q = 1) : d317684 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d315482, d316760, d317684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315482, d316760, d317684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315483 q = 1) (hb : d316761 q = 1) : d317685 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d315483, d316761, d317685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315483, d316761, d317685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315484 q = 1) (hb : d316762 q = 1) : d317686 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d315484, d316762, d317686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315484, d316762, d317686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315485 q = 1) (hb : d316763 q = 1) : d317687 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d315485, d316763, d317687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315485, d316763, d317687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83769 (p : Pattern) (ha : d39244 p = 1) (hb : d52988 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52988 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d52107 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d1519 q = 1) (hb : d52960 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1519, d52960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1519, d52960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d1531 q = 1) (hb : d52972 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1531, d52972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1531, d52972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1547 q = 1) (hb : d52988 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1547, d52988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1547, d52988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d39244 q = 1) (hb : d52988 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d39244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d39244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro83770 (p : Pattern) (ha : d52966 p = 1) (hb : d286611 p = 1) : d317692 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d307 q = 1) : d307 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d52107 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d309 q = 1) (hb : d52964 q = 1) : d1997 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d309, d52964, d1997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309, d52964, d1997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1519 q = 1) (hb : d52665 q = 1) : d1519 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1520 q = 1) (hb : d52965 q = 1) : d40834 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1520, d52965, d40834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1520, d52965, d40834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33554 q = 1) (hb : d52966 q = 1) : d317691 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d33554, d52966, d317691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33554, d52966, d317691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d52966 q = 1) (hb : d286611 q = 1) : d317692 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d286611, d317692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d286611, d317692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro83771 (p : Pattern) (ha : d286640 p = 1) (hb : d315533 p = 1) : d317727 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52966 q = 1) (hb : d286612 q = 1) : d317693 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d286612, d317693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83770 q ha hb
    | true =>
      simp only [d286612, d317693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52667 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d286613 q = 1) (hb : d315498 q = 1) : d317694 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d286613, d315498, d317694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d286613, d315498, d317694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52988 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52988 q = 1) (hb : d258107 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d258107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83769 q hb ha
    | true =>
      simp only [d258107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d258108 q = 1) (hb : d315524 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d258108, d315524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d258108, d315524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d286622 q = 1) (hb : d315525 q = 1) : d317719 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d286622, d315525, d317719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d286622, d315525, d317719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d258109 q = 1) : d258109 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d286638 q = 1) (hb : d315526 q = 1) : d317720 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d286638, d315526, d317720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d286638, d315526, d317720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d286639 q = 1) (hb : d315527 q = 1) : d317721 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d286639, d315527, d317721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d286639, d315527, d317721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d315516 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d286640 q = 1) (hb : d315533 q = 1) : d317727 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d286640, d315533, d317727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d286640, d315533, d317727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro83772 (p : Pattern) (ha : d286658 p = 1) (hb : d315551 p = 1) : d317739 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d286641 q = 1) (hb : d315534 q = 1) : d317728 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d286641, d315534, d317728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83771 q ha hb
    | true =>
      simp only [d286641, d315534, d317728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d286642 q = 1) (hb : d315535 q = 1) : d317729 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d286642, d315535, d317729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286642, d315535, d317729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d286643 q = 1) (hb : d315536 q = 1) : d317730 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d286643, d315536, d317730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d286643, d315536, d317730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d286644 q = 1) (hb : d315537 q = 1) : d317731 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d286644, d315537, d317731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d286644, d315537, d317731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d286653 q = 1) (hb : d315544 q = 1) : d317738 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d286653, d315544, d317738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d286653, d315544, d317738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d315550 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d286658 q = 1) (hb : d315551 q = 1) : d317739 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d286658, d315551, d317739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d286658, d315551, d317739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro83773 (p : Pattern) (ha : d286640 p = 1) (hb : d315517 p = 1) : d317712 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52966 q = 1) (hb : d286612 q = 1) : d317693 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d286612, d317693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83770 q ha hb
    | true =>
      simp only [d286612, d317693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52667 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d286613 q = 1) (hb : d315498 q = 1) : d317694 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d286613, d315498, d317694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d286613, d315498, d317694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d258108 q = 1) : d258108 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d286622 q = 1) (hb : d315499 q = 1) : d317709 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d286622, d315499, d317709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d286622, d315499, d317709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d258109 q = 1) : d258109 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d286638 q = 1) (hb : d315500 q = 1) : d317710 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d286638, d315500, d317710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d286638, d315500, d317710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d286639 q = 1) (hb : d315501 q = 1) : d317711 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d286639, d315501, d317711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d286639, d315501, d317711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d315516 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d286640 q = 1) (hb : d315517 q = 1) : d317712 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d286640, d315517, d317712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d286640, d315517, d317712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro83774 (p : Pattern) (ha : d53285 p = 1) (hb : d286611 p = 1) : d317692 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53285 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d307 q = 1) : d307 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d52107 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d309 q = 1) (hb : d52964 q = 1) : d1997 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d309, d52964, d1997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309, d52964, d1997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d1519 q = 1) : d1519 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d1520 q = 1) (hb : d53284 q = 1) : d40834 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1520, d53284, d40834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1520, d53284, d40834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d33554 q = 1) (hb : d53285 q = 1) : d317691 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d33554, d53285, d317691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33554, d53285, d317691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d53285 q = 1) (hb : d286611 q = 1) : d317692 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d286611, d317692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d286611, d317692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro83775 (p : Pattern) (ha : d315493 p = 1) (hb : d316770 p = 1) : d317698 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d34357 q = 1) : d34357 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53285 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53285 q = 1) (hb : d286612 q = 1) : d317693 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d286612, d317693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83774 q ha hb
    | true =>
      simp only [d286612, d317693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d286613 q = 1) (hb : d315489 q = 1) : d317694 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d286613, d315489, d317694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d286613, d315489, d317694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d315490 q = 1) (hb : d316353 q = 1) : d317695 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315490, d316353, d317695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d315490, d316353, d317695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d316767 q = 1) : d316767 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d315491 q = 1) (hb : d316768 q = 1) : d317696 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d315491, d316768, d317696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315491, d316768, d317696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d315492 q = 1) (hb : d316769 q = 1) : d317697 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d315492, d316769, d317697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d315492, d316769, d317697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h9 (q : Pattern) (ha : d315493 q = 1) (hb : d316770 q = 1) : d317698 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d315493, d316770, d317698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d315493, d316770, d317698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro83776 (p : Pattern) (ha : d315502 p = 1) (hb : d316778 p = 1) : d317703 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53285 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53285 q = 1) (hb : d286612 q = 1) : d317693 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d286612, d317693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83774 q ha hb
    | true =>
      simp only [d286612, d317693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d286613 q = 1) (hb : d315489 q = 1) : d317694 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d286613, d315489, d317694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d286613, d315489, d317694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d315490 q = 1) (hb : d316353 q = 1) : d317695 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315490, d316353, d317695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315490, d316353, d317695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d316767 q = 1) : d316767 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d315491 q = 1) (hb : d316768 q = 1) : d317696 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d315491, d316768, d317696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315491, d316768, d317696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d315492 q = 1) (hb : d316769 q = 1) : d317697 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d315492, d316769, d317697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315492, d316769, d317697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d315501 q = 1) (hb : d316777 q = 1) : d316777 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d315502 q = 1) (hb : d316778 q = 1) : d317703 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d315502, d316778, d317703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d315502, d316778, d317703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro83777 (p : Pattern) (ha : d315523 p = 1) (hb : d316790 p = 1) : d317718 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315494 q = 1) (hb : d316771 q = 1) : d317699 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315494, d316771, d317699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83775 q ha hb
    | true =>
      simp only [d315494, d316771, d317699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315495 q = 1) (hb : d316772 q = 1) : d317700 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315495, d316772, d317700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d315495, d316772, d317700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d315496 q = 1) (hb : d316773 q = 1) : d317701 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d315496, d316773, d317701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315496, d316773, d317701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315497 q = 1) (hb : d316774 q = 1) : d317702 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d315497, d316774, d317702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315497, d316774, d317702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d315503 q = 1) (hb : d316779 q = 1) : d317704 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315503, d316779, d317704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83776 q ha hb
    | true =>
      simp only [d315503, d316779, d317704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d315504 q = 1) (hb : d316780 q = 1) : d317705 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315504, d316780, d317705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315504, d316780, d317705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d315505 q = 1) (hb : d316781 q = 1) : d317706 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d315505, d316781, d317706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315505, d316781, d317706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d315506 q = 1) (hb : d316782 q = 1) : d317707 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d315506, d316782, d317707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d315506, d316782, d317707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d315507 q = 1) (hb : d316783 q = 1) : d317708 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d315507, d316783, d317708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315507, d316783, d317708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d315512 q = 1) (hb : d316788 q = 1) : d316788 q = 1 := by
    exact hb
  have h11 (q : Pattern) (ha : d286641 q = 1) (hb : d315518 q = 1) : d317713 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d286641, d315518, d317713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83773 q ha hb
    | true =>
      simp only [d286641, d315518, d317713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d286642 q = 1) (hb : d315519 q = 1) : d317714 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d286642, d315519, d317714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d286642, d315519, d317714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d286643 q = 1) (hb : d315520 q = 1) : d317715 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d286643, d315520, d317715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d286643, d315520, d317715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d286644 q = 1) (hb : d315521 q = 1) : d317716 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d286644, d315521, d317716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d286644, d315521, d317716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d315522 q = 1) (hb : d316789 q = 1) : d317717 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d315522, d316789, d317717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d315522, d316789, d317717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d315523 q = 1) (hb : d316790 q = 1) : d317718 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d315523, d316790, d317718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d315523, d316790, d317718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro83778 (p : Pattern) (ha : d315528 p = 1) (hb : d316791 p = 1) : d317722 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53285 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53285 q = 1) (hb : d286612 q = 1) : d317693 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d286612, d317693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83774 q ha hb
    | true =>
      simp only [d286612, d317693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d286613 q = 1) (hb : d315489 q = 1) : d317694 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d286613, d315489, d317694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d286613, d315489, d317694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d315490 q = 1) (hb : d316353 q = 1) : d317695 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315490, d316353, d317695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315490, d316353, d317695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d316767 q = 1) : d316767 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d315491 q = 1) (hb : d316768 q = 1) : d317696 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d315491, d316768, d317696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315491, d316768, d317696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d315492 q = 1) (hb : d316769 q = 1) : d317697 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d315492, d316769, d317697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315492, d316769, d317697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52966 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d52966 q = 1) (hb : d286612 q = 1) : d317693 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d286612, d317693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83770 q ha hb
    | true =>
      simp only [d286612, d317693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52667 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d286613 q = 1) (hb : d315498 q = 1) : d317694 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d286613, d315498, d317694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d286613, d315498, d317694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52988 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d52988 q = 1) (hb : d258107 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d258107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83769 q hb ha
    | true =>
      simp only [d258107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d258108 q = 1) (hb : d315524 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d258108, d315524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d258108, d315524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d286622 q = 1) (hb : d315525 q = 1) : d317719 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d286622, d315525, d317719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d286622, d315525, d317719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d1 q = 1) (hb : d258109 q = 1) : d258109 q = 1 := by
    exact hb
  have h17 (q : Pattern) (ha : d286638 q = 1) (hb : d315526 q = 1) : d317720 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d286638, d315526, d317720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d286638, d315526, d317720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d286639 q = 1) (hb : d315527 q = 1) : d317721 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d286639, d315527, d317721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d286639, d315527, d317721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d315528 q = 1) (hb : d316791 q = 1) : d317722 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d315528, d316791, d317722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d315528, d316791, d317722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  exact h19 p ha hb
theorem andIntro83779 (p : Pattern) (ha : d315540 p = 1) (hb : d316797 p = 1) : d317734 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315529 q = 1) (hb : d316792 q = 1) : d317723 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315529, d316792, d317723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83778 q ha hb
    | true =>
      simp only [d315529, d316792, d317723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315530 q = 1) (hb : d316793 q = 1) : d317724 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315530, d316793, d317724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d315530, d316793, d317724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d315531 q = 1) (hb : d316794 q = 1) : d317725 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d315531, d316794, d317725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315531, d316794, d317725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315532 q = 1) (hb : d316795 q = 1) : d317726 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d315532, d316795, d317726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315532, d316795, d317726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d286641 q = 1) (hb : d315534 q = 1) : d317728 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d286641, d315534, d317728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83771 q ha hb
    | true =>
      simp only [d286641, d315534, d317728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d286642 q = 1) (hb : d315535 q = 1) : d317729 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d286642, d315535, d317729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d286642, d315535, d317729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d286643 q = 1) (hb : d315536 q = 1) : d317730 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d286643, d315536, d317730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d286643, d315536, d317730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d286644 q = 1) (hb : d315537 q = 1) : d317731 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d286644, d315537, d317731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d286644, d315537, d317731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d315538 q = 1) (hb : d316796 q = 1) : d317732 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d315538, d316796, d317732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315538, d316796, d317732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d286641 q = 1) (hb : d315518 q = 1) : d317713 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d286641, d315518, d317713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83773 q ha hb
    | true =>
      simp only [d286641, d315518, d317713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d286642 q = 1) (hb : d315519 q = 1) : d317714 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d286642, d315519, d317714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d286642, d315519, d317714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d286643 q = 1) (hb : d315520 q = 1) : d317715 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d286643, d315520, d317715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d286643, d315520, d317715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d286644 q = 1) (hb : d315521 q = 1) : d317716 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d286644, d315521, d317716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d286644, d315521, d317716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d286653 q = 1) (hb : d315539 q = 1) : d317733 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d286653, d315539, d317733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d286653, d315539, d317733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d315540 q = 1) (hb : d316797 q = 1) : d317734 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d315540, d316797, d317734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d315540, d316797, d317734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro83780 (p : Pattern) (ha : d315558 p = 1) (hb : d316807 p = 1) : d317746 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315541 q = 1) (hb : d316798 q = 1) : d317735 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315541, d316798, d317735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83777 q ha hb
    | true =>
      simp only [d315541, d316798, d317735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83779 q ha hb
  have h2 (q : Pattern) (ha : d315542 q = 1) (hb : d316799 q = 1) : d317736 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315542, d316799, d317736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315542, d316799, d317736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315543 q = 1) (hb : d316800 q = 1) : d317737 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315543, d316800, d317737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315543, d316800, d317737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315552 q = 1) (hb : d316801 q = 1) : d317740 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315552, d316801, d317740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83779 q ha hb
    | true =>
      simp only [d315552, d316801, d317740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83772 q hb ha
  have h5 (q : Pattern) (ha : d315553 q = 1) (hb : d316802 q = 1) : d317741 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315553, d316802, d317741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315553, d316802, d317741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315554 q = 1) (hb : d316803 q = 1) : d317742 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315554, d316803, d317742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315554, d316803, d317742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d315555 q = 1) (hb : d316804 q = 1) : d317743 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d315555, d316804, d317743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315555, d316804, d317743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d315556 q = 1) (hb : d316805 q = 1) : d317744 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d315556, d316805, d317744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315556, d316805, d317744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d315557 q = 1) (hb : d316806 q = 1) : d317745 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d315557, d316806, d317745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d315557, d316806, d317745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d315558 q = 1) (hb : d316807 q = 1) : d317746 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d315558, d316807, d317746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d315558, d316807, d317746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro83781 (p : Pattern) (ha : d315562 p = 1) (hb : d316811 p = 1) : d317750 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315552 q = 1) (hb : d316801 q = 1) : d317740 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315552, d316801, d317740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83779 q ha hb
    | true =>
      simp only [d315552, d316801, d317740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83772 q hb ha
  have h2 (q : Pattern) (ha : d315553 q = 1) (hb : d316802 q = 1) : d317741 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315553, d316802, d317741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315553, d316802, d317741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315554 q = 1) (hb : d316803 q = 1) : d317742 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315554, d316803, d317742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315554, d316803, d317742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315556 q = 1) (hb : d316805 q = 1) : d317744 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d315556, d316805, d317744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315556, d316805, d317744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d315561 q = 1) (hb : d316810 q = 1) : d317749 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d315561, d316810, d317749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315561, d316810, d317749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d315562 q = 1) (hb : d316811 q = 1) : d317750 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d315562, d316811, d317750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315562, d316811, d317750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83782 (p : Pattern) (ha : d315568 p = 1) (hb : d316817 p = 1) : d317756 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315559 q = 1) (hb : d316808 q = 1) : d317747 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315559, d316808, d317747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83780 q ha hb
    | true =>
      simp only [d315559, d316808, d317747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315560 q = 1) (hb : d316809 q = 1) : d317748 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315560, d316809, d317748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315560, d316809, d317748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315563 q = 1) (hb : d316812 q = 1) : d317751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315563, d316812, d317751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83781 q ha hb
    | true =>
      simp only [d315563, d316812, d317751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315564 q = 1) (hb : d316813 q = 1) : d317752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315564, d316813, d317752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315564, d316813, d317752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315565 q = 1) (hb : d316814 q = 1) : d317753 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315565, d316814, d317753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315565, d316814, d317753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315566 q = 1) (hb : d316815 q = 1) : d317754 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315566, d316815, d317754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315566, d316815, d317754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d315567 q = 1) (hb : d316816 q = 1) : d317755 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315567, d316816, d317755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315567, d316816, d317755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d315568 q = 1) (hb : d316817 q = 1) : d317756 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315568, d316817, d317756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315568, d316817, d317756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83783 (p : Pattern) (ha : d315572 p = 1) (hb : d316821 p = 1) : d317760 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315563 q = 1) (hb : d316812 q = 1) : d317751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315563, d316812, d317751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83781 q ha hb
    | true =>
      simp only [d315563, d316812, d317751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315564 q = 1) (hb : d316813 q = 1) : d317752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315564, d316813, d317752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315564, d316813, d317752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315569 q = 1) (hb : d316818 q = 1) : d317757 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315569, d316818, d317757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315569, d316818, d317757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315570 q = 1) (hb : d316819 q = 1) : d317758 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315570, d316819, d317758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315570, d316819, d317758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d315571 q = 1) (hb : d316820 q = 1) : d317759 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315571, d316820, d317759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315571, d316820, d317759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d315572 q = 1) (hb : d316821 q = 1) : d317760 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315572, d316821, d317760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315572, d316821, d317760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83784 (p : Pattern) (ha : d315578 p = 1) (hb : d316827 p = 1) : d317766 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315573 q = 1) (hb : d316822 q = 1) : d317761 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315573, d316822, d317761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83782 q ha hb
    | true =>
      simp only [d315573, d316822, d317761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83783 q ha hb
  have h2 (q : Pattern) (ha : d315574 q = 1) (hb : d316823 q = 1) : d317762 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315574, d316823, d317762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315574, d316823, d317762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315575 q = 1) (hb : d316824 q = 1) : d317763 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315575, d316824, d317763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315575, d316824, d317763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315576 q = 1) (hb : d316825 q = 1) : d317764 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315576, d316825, d317764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315576, d316825, d317764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315577 q = 1) (hb : d316826 q = 1) : d317765 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d315577, d316826, d317765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315577, d316826, d317765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315578 q = 1) (hb : d316827 q = 1) : d317766 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d315578, d316827, d317766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315578, d316827, d317766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83785 (p : Pattern) (ha : d315581 p = 1) (hb : d316830 p = 1) : d317769 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315559 q = 1) (hb : d316808 q = 1) : d317747 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315559, d316808, d317747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83780 q ha hb
    | true =>
      simp only [d315559, d316808, d317747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315560 q = 1) (hb : d316809 q = 1) : d317748 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315560, d316809, d317748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315560, d316809, d317748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315563 q = 1) (hb : d316812 q = 1) : d317751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315563, d316812, d317751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83781 q ha hb
    | true =>
      simp only [d315563, d316812, d317751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315564 q = 1) (hb : d316813 q = 1) : d317752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315564, d316813, d317752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315564, d316813, d317752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315565 q = 1) (hb : d316814 q = 1) : d317753 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315565, d316814, d317753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315565, d316814, d317753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315566 q = 1) (hb : d316815 q = 1) : d317754 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315566, d316815, d317754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315566, d316815, d317754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d315567 q = 1) (hb : d316816 q = 1) : d317755 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315567, d316816, d317755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315567, d316816, d317755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d315581 q = 1) (hb : d316830 q = 1) : d317769 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315581, d316830, d317769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d315581, d316830, d317769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro83786 (p : Pattern) (ha : d315582 p = 1) (hb : d316831 p = 1) : d317770 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315563 q = 1) (hb : d316812 q = 1) : d317751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315563, d316812, d317751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83781 q ha hb
    | true =>
      simp only [d315563, d316812, d317751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315564 q = 1) (hb : d316813 q = 1) : d317752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315564, d316813, d317752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315564, d316813, d317752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315569 q = 1) (hb : d316818 q = 1) : d317757 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315569, d316818, d317757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315569, d316818, d317757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315570 q = 1) (hb : d316819 q = 1) : d317758 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315570, d316819, d317758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315570, d316819, d317758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d315571 q = 1) (hb : d316820 q = 1) : d317759 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315571, d316820, d317759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315571, d316820, d317759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d315582 q = 1) (hb : d316831 q = 1) : d317770 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315582, d316831, d317770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315582, d316831, d317770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83787 (p : Pattern) (ha : d315588 p = 1) (hb : d316837 p = 1) : d317776 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315573 q = 1) (hb : d316822 q = 1) : d317761 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315573, d316822, d317761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83782 q ha hb
    | true =>
      simp only [d315573, d316822, d317761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83783 q ha hb
  have h2 (q : Pattern) (ha : d315574 q = 1) (hb : d316823 q = 1) : d317762 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315574, d316823, d317762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315574, d316823, d317762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315575 q = 1) (hb : d316824 q = 1) : d317763 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315575, d316824, d317763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315575, d316824, d317763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315576 q = 1) (hb : d316825 q = 1) : d317764 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315576, d316825, d317764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315576, d316825, d317764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315577 q = 1) (hb : d316826 q = 1) : d317765 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d315577, d316826, d317765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315577, d316826, d317765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315583 q = 1) (hb : d316832 q = 1) : d317771 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315583, d316832, d317771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83785 q ha hb
    | true =>
      simp only [d315583, d316832, d317771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83786 q ha hb
  have h7 (q : Pattern) (ha : d315584 q = 1) (hb : d316833 q = 1) : d317772 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315584, d316833, d317772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315584, d316833, d317772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d315585 q = 1) (hb : d316834 q = 1) : d317773 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315585, d316834, d317773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d315585, d316834, d317773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d315586 q = 1) (hb : d316835 q = 1) : d317774 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315586, d316835, d317774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315586, d316835, d317774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d315587 q = 1) (hb : d316836 q = 1) : d317775 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d315587, d316836, d317775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315587, d316836, d317775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d315588 q = 1) (hb : d316837 q = 1) : d317776 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d315588, d316837, d317776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315588, d316837, d317776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro83788 (p : Pattern) (ha : d315593 p = 1) (hb : d316842 p = 1) : d317781 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315559 q = 1) (hb : d316808 q = 1) : d317747 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315559, d316808, d317747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83780 q ha hb
    | true =>
      simp only [d315559, d316808, d317747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315560 q = 1) (hb : d316809 q = 1) : d317748 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315560, d316809, d317748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315560, d316809, d317748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315563 q = 1) (hb : d316812 q = 1) : d317751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315563, d316812, d317751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83781 q ha hb
    | true =>
      simp only [d315563, d316812, d317751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315564 q = 1) (hb : d316813 q = 1) : d317752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315564, d316813, d317752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315564, d316813, d317752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315565 q = 1) (hb : d316814 q = 1) : d317753 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315565, d316814, d317753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315565, d316814, d317753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315566 q = 1) (hb : d316815 q = 1) : d317754 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315566, d316815, d317754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315566, d316815, d317754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d315592 q = 1) (hb : d316841 q = 1) : d317780 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315592, d316841, d317780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315592, d316841, d317780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d315593 q = 1) (hb : d316842 q = 1) : d317781 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315593, d316842, d317781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315593, d316842, d317781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83789 (p : Pattern) (ha : d315595 p = 1) (hb : d316844 p = 1) : d317783 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315563 q = 1) (hb : d316812 q = 1) : d317751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315563, d316812, d317751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83781 q ha hb
    | true =>
      simp only [d315563, d316812, d317751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315564 q = 1) (hb : d316813 q = 1) : d317752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315564, d316813, d317752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315564, d316813, d317752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315569 q = 1) (hb : d316818 q = 1) : d317757 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315569, d316818, d317757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315569, d316818, d317757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315570 q = 1) (hb : d316819 q = 1) : d317758 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315570, d316819, d317758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315570, d316819, d317758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d315594 q = 1) (hb : d316843 q = 1) : d317782 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315594, d316843, d317782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315594, d316843, d317782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315595 q = 1) (hb : d316844 q = 1) : d317783 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315595, d316844, d317783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315595, d316844, d317783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83790 (p : Pattern) (ha : d315602 p = 1) (hb : d316851 p = 1) : d317790 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315559 q = 1) (hb : d316808 q = 1) : d317747 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315559, d316808, d317747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83780 q ha hb
    | true =>
      simp only [d315559, d316808, d317747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315560 q = 1) (hb : d316809 q = 1) : d317748 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315560, d316809, d317748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315560, d316809, d317748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315563 q = 1) (hb : d316812 q = 1) : d317751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315563, d316812, d317751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83781 q ha hb
    | true =>
      simp only [d315563, d316812, d317751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315564 q = 1) (hb : d316813 q = 1) : d317752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315564, d316813, d317752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315564, d316813, d317752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315565 q = 1) (hb : d316814 q = 1) : d317753 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315565, d316814, d317753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315565, d316814, d317753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315600 q = 1) (hb : d316849 q = 1) : d317788 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315600, d316849, d317788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315600, d316849, d317788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d315601 q = 1) (hb : d316850 q = 1) : d317789 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315601, d316850, d317789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315601, d316850, d317789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d315602 q = 1) (hb : d316851 q = 1) : d317790 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315602, d316851, d317790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315602, d316851, d317790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83791 (p : Pattern) (ha : d315605 p = 1) (hb : d316854 p = 1) : d317793 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315563 q = 1) (hb : d316812 q = 1) : d317751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315563, d316812, d317751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83781 q ha hb
    | true =>
      simp only [d315563, d316812, d317751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315564 q = 1) (hb : d316813 q = 1) : d317752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315564, d316813, d317752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315564, d316813, d317752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315569 q = 1) (hb : d316818 q = 1) : d317757 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315569, d316818, d317757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315569, d316818, d317757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315603 q = 1) (hb : d316852 q = 1) : d317791 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315603, d316852, d317791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315603, d316852, d317791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315604 q = 1) (hb : d316853 q = 1) : d317792 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315604, d316853, d317792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315604, d316853, d317792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d315605 q = 1) (hb : d316854 q = 1) : d317793 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315605, d316854, d317793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315605, d316854, d317793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83792 (p : Pattern) (ha : d315615 p = 1) (hb : d316879 p = 1) : d317800 p = 1 := by
  have h0 (q : Pattern) (ha : d315506 q = 1) (hb : d316788 q = 1) : d316788 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d286641 q = 1) (hb : d315518 q = 1) : d317713 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d286641, d315518, d317713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83773 q ha hb
    | true =>
      simp only [d286641, d315518, d317713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d286642 q = 1) (hb : d315519 q = 1) : d317714 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d286642, d315519, d317714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d286642, d315519, d317714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d286643 q = 1) (hb : d315520 q = 1) : d317715 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d286643, d315520, d317715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286643, d315520, d317715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d286644 q = 1) (hb : d315521 q = 1) : d317716 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d286644, d315521, d317716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d286644, d315521, d317716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d315614 q = 1) (hb : d316789 q = 1) : d317717 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d315614, d316789, d317717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d315614, d316789, d317717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d286653 q = 1) (hb : d315539 q = 1) : d317733 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d286653, d315539, d317733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d286653, d315539, d317733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d315615 q = 1) (hb : d316879 q = 1) : d317800 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d315615, d316879, d317800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315615, d316879, d317800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro83793 (p : Pattern) (ha : d315621 p = 1) (hb : d316885 p = 1) : d317806 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315610 q = 1) (hb : d316875 q = 1) : d316875 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d315611 q = 1) (hb : d316876 q = 1) : d317797 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315611, d316876, d317797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d315611, d316876, d317797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83777 q ha hb
  have h3 (q : Pattern) (ha : d315612 q = 1) (hb : d316877 q = 1) : d317798 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315612, d316877, d317798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315612, d316877, d317798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315613 q = 1) (hb : d316878 q = 1) : d317799 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315613, d316878, d317799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315613, d316878, d317799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315616 q = 1) (hb : d316880 q = 1) : d317801 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315616, d316880, d317801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83777 q ha hb
    | true =>
      simp only [d315616, d316880, d317801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83792 q ha hb
  have h6 (q : Pattern) (ha : d315617 q = 1) (hb : d316881 q = 1) : d317802 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315617, d316881, d317802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315617, d316881, d317802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d315618 q = 1) (hb : d316882 q = 1) : d317803 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315618, d316882, d317803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315618, d316882, d317803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d315619 q = 1) (hb : d316883 q = 1) : d317804 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d315619, d316883, d317804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315619, d316883, d317804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d315541 q = 1) (hb : d316798 q = 1) : d317735 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315541, d316798, d317735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83777 q ha hb
    | true =>
      simp only [d315541, d316798, d317735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83779 q ha hb
  have h10 (q : Pattern) (ha : d315542 q = 1) (hb : d316799 q = 1) : d317736 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315542, d316799, d317736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315542, d316799, d317736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d315543 q = 1) (hb : d316800 q = 1) : d317737 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315543, d316800, d317737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315543, d316800, d317737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d315552 q = 1) (hb : d316801 q = 1) : d317740 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315552, d316801, d317740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83779 q ha hb
    | true =>
      simp only [d315552, d316801, d317740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83772 q hb ha
  have h13 (q : Pattern) (ha : d315553 q = 1) (hb : d316802 q = 1) : d317741 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315553, d316802, d317741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315553, d316802, d317741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d315554 q = 1) (hb : d316803 q = 1) : d317742 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315554, d316803, d317742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315554, d316803, d317742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d315555 q = 1) (hb : d316804 q = 1) : d317743 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d315555, d316804, d317743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d315555, d316804, d317743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d315620 q = 1) (hb : d316884 q = 1) : d317805 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d315620, d316884, d317805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d315620, d316884, d317805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d315621 q = 1) (hb : d316885 q = 1) : d317806 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d315621, d316885, d317806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d315621, d316885, d317806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h17 p ha hb
theorem andIntro83794 (p : Pattern) (ha : d315627 p = 1) (hb : d316891 p = 1) : d317812 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315622 q = 1) (hb : d316886 q = 1) : d317807 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315622, d316886, d317807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83793 q ha hb
    | true =>
      simp only [d315622, d316886, d317807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315623 q = 1) (hb : d316887 q = 1) : d317808 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315623, d316887, d317808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315623, d316887, d317808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315559 q = 1) (hb : d316808 q = 1) : d317747 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315559, d316808, d317747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83780 q ha hb
    | true =>
      simp only [d315559, d316808, d317747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315560 q = 1) (hb : d316809 q = 1) : d317748 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315560, d316809, d317748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315560, d316809, d317748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315624 q = 1) (hb : d316888 q = 1) : d317809 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315624, d316888, d317809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315624, d316888, d317809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315625 q = 1) (hb : d316889 q = 1) : d317810 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315625, d316889, d317810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315625, d316889, d317810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d315626 q = 1) (hb : d316890 q = 1) : d317811 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315626, d316890, d317811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315626, d316890, d317811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d315627 q = 1) (hb : d316891 q = 1) : d317812 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315627, d316891, d317812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315627, d316891, d317812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83795 (p : Pattern) (ha : d286640 p = 1) (hb : d315640 p = 1) : d317727 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52966 q = 1) (hb : d286612 q = 1) : d317693 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d286612, d317693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83770 q ha hb
    | true =>
      simp only [d286612, d317693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52667 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d286613 q = 1) (hb : d315498 q = 1) : d317694 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d286613, d315498, d317694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d286613, d315498, d317694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52988 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52988 q = 1) (hb : d258107 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d258107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83769 q hb ha
    | true =>
      simp only [d258107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d258108 q = 1) (hb : d315524 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d258108, d315524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d258108, d315524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d286622 q = 1) (hb : d315525 q = 1) : d317719 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d286622, d315525, d317719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d286622, d315525, d317719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d258109 q = 1) : d258109 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d286638 q = 1) (hb : d315526 q = 1) : d317720 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d286638, d315526, d317720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d286638, d315526, d317720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d286639 q = 1) (hb : d315527 q = 1) : d317721 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d286639, d315527, d317721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d286639, d315527, d317721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d315632 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d286640 q = 1) (hb : d315640 q = 1) : d317727 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d286640, d315640, d317727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d286640, d315640, d317727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro83796 (p : Pattern) (ha : d286658 p = 1) (hb : d315646 p = 1) : d317739 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d286641 q = 1) (hb : d315641 q = 1) : d317728 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d286641, d315641, d317728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83795 q ha hb
    | true =>
      simp only [d286641, d315641, d317728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d286642 q = 1) (hb : d315642 q = 1) : d317729 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d286642, d315642, d317729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286642, d315642, d317729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d286643 q = 1) (hb : d315643 q = 1) : d317730 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d286643, d315643, d317730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d286643, d315643, d317730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d286644 q = 1) (hb : d315644 q = 1) : d317731 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d286644, d315644, d317731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d286644, d315644, d317731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d286653 q = 1) (hb : d315645 q = 1) : d317738 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d286653, d315645, d317738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d286653, d315645, d317738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d286658 q = 1) (hb : d315646 q = 1) : d317739 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d286658, d315646, d317739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d286658, d315646, d317739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro83797 (p : Pattern) (ha : d286640 p = 1) (hb : d315633 p = 1) : d317712 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52966 q = 1) (hb : d286612 q = 1) : d317693 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d286612, d317693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83770 q ha hb
    | true =>
      simp only [d286612, d317693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52667 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d286613 q = 1) (hb : d315498 q = 1) : d317694 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d286613, d315498, d317694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d286613, d315498, d317694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1 q = 1) (hb : d258108 q = 1) : d258108 q = 1 := by
    exact hb
  have h5 (q : Pattern) (ha : d286622 q = 1) (hb : d315499 q = 1) : d317709 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d286622, d315499, d317709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d286622, d315499, d317709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d258109 q = 1) : d258109 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d286638 q = 1) (hb : d315500 q = 1) : d317710 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d286638, d315500, d317710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d286638, d315500, d317710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d286639 q = 1) (hb : d315501 q = 1) : d317711 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d286639, d315501, d317711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d286639, d315501, d317711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d315632 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d286640 q = 1) (hb : d315633 q = 1) : d317712 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d286640, d315633, d317712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d286640, d315633, d317712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro83798 (p : Pattern) (ha : d315639 p = 1) (hb : d316797 p = 1) : d317734 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315529 q = 1) (hb : d316792 q = 1) : d317723 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315529, d316792, d317723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83778 q ha hb
    | true =>
      simp only [d315529, d316792, d317723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315530 q = 1) (hb : d316793 q = 1) : d317724 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315530, d316793, d317724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d315530, d316793, d317724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d315531 q = 1) (hb : d316794 q = 1) : d317725 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d315531, d316794, d317725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315531, d316794, d317725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315532 q = 1) (hb : d316795 q = 1) : d317726 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d315532, d316795, d317726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315532, d316795, d317726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d286641 q = 1) (hb : d315534 q = 1) : d317728 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d286641, d315534, d317728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83771 q ha hb
    | true =>
      simp only [d286641, d315534, d317728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d286642 q = 1) (hb : d315535 q = 1) : d317729 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d286642, d315535, d317729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d286642, d315535, d317729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d286643 q = 1) (hb : d315536 q = 1) : d317730 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d286643, d315536, d317730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d286643, d315536, d317730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d286644 q = 1) (hb : d315537 q = 1) : d317731 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d286644, d315537, d317731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d286644, d315537, d317731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d315538 q = 1) (hb : d316796 q = 1) : d317732 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d315538, d316796, d317732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315538, d316796, d317732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d286641 q = 1) (hb : d315634 q = 1) : d317713 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d286641, d315634, d317713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83797 q ha hb
    | true =>
      simp only [d286641, d315634, d317713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d286642 q = 1) (hb : d315635 q = 1) : d317714 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d286642, d315635, d317714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d286642, d315635, d317714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d286643 q = 1) (hb : d315636 q = 1) : d317715 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d286643, d315636, d317715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d286643, d315636, d317715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d286644 q = 1) (hb : d315637 q = 1) : d317716 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d286644, d315637, d317716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d286644, d315637, d317716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d286653 q = 1) (hb : d315638 q = 1) : d317733 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d286653, d315638, d317733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d286653, d315638, d317733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d315639 q = 1) (hb : d316797 q = 1) : d317734 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d315639, d316797, d317734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d315639, d316797, d317734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro83799 (p : Pattern) (ha : d315652 p = 1) (hb : d316807 p = 1) : d317746 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315541 q = 1) (hb : d316798 q = 1) : d317735 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315541, d316798, d317735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83777 q ha hb
    | true =>
      simp only [d315541, d316798, d317735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83779 q ha hb
  have h2 (q : Pattern) (ha : d315542 q = 1) (hb : d316799 q = 1) : d317736 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315542, d316799, d317736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315542, d316799, d317736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315543 q = 1) (hb : d316800 q = 1) : d317737 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315543, d316800, d317737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315543, d316800, d317737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315552 q = 1) (hb : d316801 q = 1) : d317740 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315552, d316801, d317740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83779 q ha hb
    | true =>
      simp only [d315552, d316801, d317740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83772 q hb ha
  have h5 (q : Pattern) (ha : d315553 q = 1) (hb : d316802 q = 1) : d317741 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315553, d316802, d317741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315553, d316802, d317741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315554 q = 1) (hb : d316803 q = 1) : d317742 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315554, d316803, d317742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315554, d316803, d317742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d315555 q = 1) (hb : d316804 q = 1) : d317743 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d315555, d316804, d317743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315555, d316804, d317743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d315647 q = 1) (hb : d316801 q = 1) : d317740 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315647, d316801, d317740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83798 q ha hb
    | true =>
      simp only [d315647, d316801, d317740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83796 q hb ha
  have h9 (q : Pattern) (ha : d315648 q = 1) (hb : d316802 q = 1) : d317741 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315648, d316802, d317741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315648, d316802, d317741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d315649 q = 1) (hb : d316803 q = 1) : d317742 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315649, d316803, d317742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315649, d316803, d317742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d315650 q = 1) (hb : d316805 q = 1) : d317744 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d315650, d316805, d317744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d315650, d316805, d317744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d315651 q = 1) (hb : d316806 q = 1) : d317745 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d315651, d316806, d317745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d315651, d316806, d317745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d315652 q = 1) (hb : d316807 q = 1) : d317746 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d315652, d316807, d317746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d315652, d316807, d317746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro83800 (p : Pattern) (ha : d315658 p = 1) (hb : d316897 p = 1) : d317818 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315653 q = 1) (hb : d316808 q = 1) : d317747 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315653, d316808, d317747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83799 q ha hb
    | true =>
      simp only [d315653, d316808, d317747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315654 q = 1) (hb : d316809 q = 1) : d317748 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315654, d316809, d317748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315654, d316809, d317748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315655 q = 1) (hb : d316894 q = 1) : d317815 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315655, d316894, d317815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315655, d316894, d317815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315656 q = 1) (hb : d316895 q = 1) : d317816 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315656, d316895, d317816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315656, d316895, d317816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d315657 q = 1) (hb : d316896 q = 1) : d317817 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315657, d316896, d317817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315657, d316896, d317817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d315658 q = 1) (hb : d316897 q = 1) : d317818 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315658, d316897, d317818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315658, d316897, d317818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83801 (p : Pattern) (ha : d315664 p = 1) (hb : d316903 p = 1) : d317824 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315596 q = 1) (hb : d316845 q = 1) : d317784 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315596, d316845, d317784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83788 q ha hb
    | true =>
      simp only [d315596, d316845, d317784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83789 q ha hb
  have h2 (q : Pattern) (ha : d315597 q = 1) (hb : d316846 q = 1) : d317785 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315597, d316846, d317785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315597, d316846, d317785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315598 q = 1) (hb : d316847 q = 1) : d317786 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315598, d316847, d317786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315598, d316847, d317786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315599 q = 1) (hb : d316848 q = 1) : d317787 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315599, d316848, d317787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315599, d316848, d317787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315606 q = 1) (hb : d316855 q = 1) : d317794 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315606, d316855, d317794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83790 q ha hb
    | true =>
      simp only [d315606, d316855, d317794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83791 q ha hb
  have h6 (q : Pattern) (ha : d315607 q = 1) (hb : d316856 q = 1) : d317795 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315607, d316856, d317795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315607, d316856, d317795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d315608 q = 1) (hb : d316857 q = 1) : d317796 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315608, d316857, d317796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315608, d316857, d317796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d315628 q = 1) (hb : d316892 q = 1) : d317813 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315628, d316892, d317813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83794 q ha hb
    | true =>
      simp only [d315628, d316892, d317813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83782 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d315573 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d315629 q = 1) (hb : d316893 q = 1) : d317814 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315629, d316893, d317814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d315629, d316893, d317814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d315659 q = 1) (hb : d316898 q = 1) : d317819 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315659, d316898, d317819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83800 q ha hb
    | true =>
      simp only [d315659, d316898, d317819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d315660 q = 1) (hb : d316899 q = 1) : d317820 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315660, d316899, d317820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d315660, d316899, d317820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d315661 q = 1) (hb : d316900 q = 1) : d317821 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315661, d316900, d317821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d315661, d316900, d317821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d315662 q = 1) (hb : d316901 q = 1) : d317822 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315662, d316901, d317822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d315662, d316901, d317822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d315663 q = 1) (hb : d316902 q = 1) : d317823 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d315663, d316902, d317823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315663, d316902, d317823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d315664 q = 1) (hb : d316903 q = 1) : d317824 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d315664, d316903, d317824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315664, d316903, d317824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro83802 (p : Pattern) (ha : d315665 p = 1) (hb : d316904 p = 1) : d317825 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315559 q = 1) (hb : d316808 q = 1) : d317747 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315559, d316808, d317747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83780 q ha hb
    | true =>
      simp only [d315559, d316808, d317747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315560 q = 1) (hb : d316809 q = 1) : d317748 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315560, d316809, d317748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315560, d316809, d317748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315563 q = 1) (hb : d316812 q = 1) : d317751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315563, d316812, d317751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83781 q ha hb
    | true =>
      simp only [d315563, d316812, d317751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315564 q = 1) (hb : d316813 q = 1) : d317752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315564, d316813, d317752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315564, d316813, d317752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315565 q = 1) (hb : d316814 q = 1) : d317753 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315565, d316814, d317753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315565, d316814, d317753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315566 q = 1) (hb : d316815 q = 1) : d317754 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315566, d316815, d317754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315566, d316815, d317754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d315592 q = 1) (hb : d316841 q = 1) : d317780 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315592, d316841, d317780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315592, d316841, d317780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d315665 q = 1) (hb : d316904 q = 1) : d317825 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315665, d316904, d317825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d315665, d316904, d317825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro83803 (p : Pattern) (ha : d315666 p = 1) (hb : d316905 p = 1) : d317826 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315563 q = 1) (hb : d316812 q = 1) : d317751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315563, d316812, d317751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83781 q ha hb
    | true =>
      simp only [d315563, d316812, d317751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315564 q = 1) (hb : d316813 q = 1) : d317752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315564, d316813, d317752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315564, d316813, d317752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315569 q = 1) (hb : d316818 q = 1) : d317757 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315569, d316818, d317757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315569, d316818, d317757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315570 q = 1) (hb : d316819 q = 1) : d317758 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315570, d316819, d317758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315570, d316819, d317758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d315594 q = 1) (hb : d316843 q = 1) : d317782 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315594, d316843, d317782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315594, d316843, d317782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315666 q = 1) (hb : d316905 q = 1) : d317826 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315666, d316905, d317826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315666, d316905, d317826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83804 (p : Pattern) (ha : d315671 p = 1) (hb : d316910 p = 1) : d317831 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315559 q = 1) (hb : d316808 q = 1) : d317747 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315559, d316808, d317747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83780 q ha hb
    | true =>
      simp only [d315559, d316808, d317747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315560 q = 1) (hb : d316809 q = 1) : d317748 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315560, d316809, d317748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315560, d316809, d317748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315563 q = 1) (hb : d316812 q = 1) : d317751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315563, d316812, d317751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83781 q ha hb
    | true =>
      simp only [d315563, d316812, d317751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315564 q = 1) (hb : d316813 q = 1) : d317752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315564, d316813, d317752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315564, d316813, d317752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315565 q = 1) (hb : d316814 q = 1) : d317753 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315565, d316814, d317753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315565, d316814, d317753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315600 q = 1) (hb : d316849 q = 1) : d317788 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315600, d316849, d317788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315600, d316849, d317788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d315601 q = 1) (hb : d316850 q = 1) : d317789 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315601, d316850, d317789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315601, d316850, d317789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d315671 q = 1) (hb : d316910 q = 1) : d317831 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315671, d316910, d317831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d315671, d316910, d317831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro83805 (p : Pattern) (ha : d315672 p = 1) (hb : d316911 p = 1) : d317832 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315563 q = 1) (hb : d316812 q = 1) : d317751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315563, d316812, d317751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83781 q ha hb
    | true =>
      simp only [d315563, d316812, d317751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315564 q = 1) (hb : d316813 q = 1) : d317752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315564, d316813, d317752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315564, d316813, d317752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315569 q = 1) (hb : d316818 q = 1) : d317757 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315569, d316818, d317757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315569, d316818, d317757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315603 q = 1) (hb : d316852 q = 1) : d317791 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315603, d316852, d317791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315603, d316852, d317791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315604 q = 1) (hb : d316853 q = 1) : d317792 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315604, d316853, d317792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315604, d316853, d317792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d315672 q = 1) (hb : d316911 q = 1) : d317832 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315672, d316911, d317832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315672, d316911, d317832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83806 (p : Pattern) (ha : d315676 p = 1) (hb : d316915 p = 1) : d317836 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315622 q = 1) (hb : d316886 q = 1) : d317807 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315622, d316886, d317807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83793 q ha hb
    | true =>
      simp only [d315622, d316886, d317807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315623 q = 1) (hb : d316887 q = 1) : d317808 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315623, d316887, d317808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315623, d316887, d317808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315559 q = 1) (hb : d316808 q = 1) : d317747 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315559, d316808, d317747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83780 q ha hb
    | true =>
      simp only [d315559, d316808, d317747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315560 q = 1) (hb : d316809 q = 1) : d317748 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315560, d316809, d317748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315560, d316809, d317748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315624 q = 1) (hb : d316888 q = 1) : d317809 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315624, d316888, d317809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315624, d316888, d317809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315625 q = 1) (hb : d316889 q = 1) : d317810 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315625, d316889, d317810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315625, d316889, d317810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d315626 q = 1) (hb : d316890 q = 1) : d317811 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315626, d316890, d317811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315626, d316890, d317811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d315676 q = 1) (hb : d316915 q = 1) : d317836 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315676, d316915, d317836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d315676, d316915, d317836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro83807 (p : Pattern) (ha : d315679 p = 1) (hb : d316918 p = 1) : d317839 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315653 q = 1) (hb : d316808 q = 1) : d317747 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315653, d316808, d317747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83799 q ha hb
    | true =>
      simp only [d315653, d316808, d317747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315654 q = 1) (hb : d316809 q = 1) : d317748 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315654, d316809, d317748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315654, d316809, d317748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315655 q = 1) (hb : d316894 q = 1) : d317815 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315655, d316894, d317815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315655, d316894, d317815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315656 q = 1) (hb : d316895 q = 1) : d317816 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315656, d316895, d317816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315656, d316895, d317816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d315657 q = 1) (hb : d316896 q = 1) : d317817 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315657, d316896, d317817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315657, d316896, d317817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d315679 q = 1) (hb : d316918 q = 1) : d317839 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315679, d316918, d317839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315679, d316918, d317839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83808 (p : Pattern) (ha : d315685 p = 1) (hb : d316924 p = 1) : d317845 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315596 q = 1) (hb : d316845 q = 1) : d317784 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315596, d316845, d317784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83788 q ha hb
    | true =>
      simp only [d315596, d316845, d317784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83789 q ha hb
  have h2 (q : Pattern) (ha : d315597 q = 1) (hb : d316846 q = 1) : d317785 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315597, d316846, d317785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315597, d316846, d317785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315598 q = 1) (hb : d316847 q = 1) : d317786 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315598, d316847, d317786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315598, d316847, d317786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315599 q = 1) (hb : d316848 q = 1) : d317787 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315599, d316848, d317787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315599, d316848, d317787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315606 q = 1) (hb : d316855 q = 1) : d317794 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315606, d316855, d317794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83790 q ha hb
    | true =>
      simp only [d315606, d316855, d317794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83791 q ha hb
  have h6 (q : Pattern) (ha : d315607 q = 1) (hb : d316856 q = 1) : d317795 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315607, d316856, d317795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315607, d316856, d317795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d315608 q = 1) (hb : d316857 q = 1) : d317796 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315608, d316857, d317796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315608, d316857, d317796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d315628 q = 1) (hb : d316892 q = 1) : d317813 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315628, d316892, d317813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83794 q ha hb
    | true =>
      simp only [d315628, d316892, d317813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83782 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d315573 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d315629 q = 1) (hb : d316893 q = 1) : d317814 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315629, d316893, d317814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d315629, d316893, d317814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d315659 q = 1) (hb : d316898 q = 1) : d317819 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315659, d316898, d317819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83800 q ha hb
    | true =>
      simp only [d315659, d316898, d317819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d315660 q = 1) (hb : d316899 q = 1) : d317820 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315660, d316899, d317820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d315660, d316899, d317820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d315661 q = 1) (hb : d316900 q = 1) : d317821 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315661, d316900, d317821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d315661, d316900, d317821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d315662 q = 1) (hb : d316901 q = 1) : d317822 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315662, d316901, d317822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d315662, d316901, d317822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d315663 q = 1) (hb : d316902 q = 1) : d317823 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d315663, d316902, d317823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315663, d316902, d317823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d315667 q = 1) (hb : d316906 q = 1) : d317827 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315667, d316906, d317827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83802 q ha hb
    | true =>
      simp only [d315667, d316906, d317827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83803 q ha hb
  have h17 (q : Pattern) (ha : d315668 q = 1) (hb : d316907 q = 1) : d317828 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315668, d316907, d317828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315668, d316907, d317828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d315669 q = 1) (hb : d316908 q = 1) : d317829 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315669, d316908, d317829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d315669, d316908, d317829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d315670 q = 1) (hb : d316909 q = 1) : d317830 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315670, d316909, d317830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315670, d316909, d317830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d315673 q = 1) (hb : d316912 q = 1) : d317833 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315673, d316912, d317833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83804 q ha hb
    | true =>
      simp only [d315673, d316912, d317833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83805 q ha hb
  have h21 (q : Pattern) (ha : d315674 q = 1) (hb : d316913 q = 1) : d317834 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315674, d316913, d317834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315674, d316913, d317834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d315675 q = 1) (hb : d316914 q = 1) : d317835 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315675, d316914, d317835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d315675, d316914, d317835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d315677 q = 1) (hb : d316916 q = 1) : d317837 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315677, d316916, d317837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83806 q ha hb
    | true =>
      simp only [d315677, d316916, d317837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83785 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d315583 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d315678 q = 1) (hb : d316917 q = 1) : d317838 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315678, d316917, d317838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d315678, d316917, d317838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d315680 q = 1) (hb : d316919 q = 1) : d317840 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315680, d316919, d317840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83807 q ha hb
    | true =>
      simp only [d315680, d316919, d317840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d315681 q = 1) (hb : d316920 q = 1) : d317841 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315681, d316920, d317841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d315681, d316920, d317841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d315682 q = 1) (hb : d316921 q = 1) : d317842 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315682, d316921, d317842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d315682, d316921, d317842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d315683 q = 1) (hb : d316922 q = 1) : d317843 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315683, d316922, d317843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d315683, d316922, d317843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d315684 q = 1) (hb : d316923 q = 1) : d317844 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d315684, d316923, d317844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d315684, d316923, d317844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d315685 q = 1) (hb : d316924 q = 1) : d317845 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d315685, d316924, d317845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d315685, d316924, d317845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro83809 (p : Pattern) (ha : d315692 p = 1) (hb : d316931 p = 1) : d317852 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315573 q = 1) (hb : d316822 q = 1) : d317761 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315573, d316822, d317761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83782 q ha hb
    | true =>
      simp only [d315573, d316822, d317761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83783 q ha hb
  have h2 (q : Pattern) (ha : d315574 q = 1) (hb : d316823 q = 1) : d317762 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315574, d316823, d317762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315574, d316823, d317762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315575 q = 1) (hb : d316824 q = 1) : d317763 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315575, d316824, d317763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315575, d316824, d317763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315576 q = 1) (hb : d316825 q = 1) : d317764 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315576, d316825, d317764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315576, d316825, d317764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315577 q = 1) (hb : d316826 q = 1) : d317765 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d315577, d316826, d317765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315577, d316826, d317765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315687 q = 1) (hb : d316926 q = 1) : d317847 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315687, d316926, d317847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83783 q ha hb
    | true =>
      simp only [d315687, d316926, d317847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d315688 q = 1) (hb : d316927 q = 1) : d317848 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315688, d316927, d317848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315688, d316927, d317848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d315689 q = 1) (hb : d316928 q = 1) : d317849 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315689, d316928, d317849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d315689, d316928, d317849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d315690 q = 1) (hb : d316929 q = 1) : d317850 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315690, d316929, d317850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315690, d316929, d317850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d315691 q = 1) (hb : d316930 q = 1) : d317851 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d315691, d316930, d317851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315691, d316930, d317851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d315692 q = 1) (hb : d316931 q = 1) : d317852 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d315692, d316931, d317852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315692, d316931, d317852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro83810 (p : Pattern) (ha : d315698 p = 1) (hb : d316937 p = 1) : d317858 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315687 q = 1) (hb : d316926 q = 1) : d317847 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315687, d316926, d317847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83783 q ha hb
    | true =>
      simp only [d315687, d316926, d317847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315688 q = 1) (hb : d316927 q = 1) : d317848 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315688, d316927, d317848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315688, d316927, d317848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315689 q = 1) (hb : d316928 q = 1) : d317849 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315689, d316928, d317849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315689, d316928, d317849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315690 q = 1) (hb : d316929 q = 1) : d317850 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315690, d316929, d317850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315690, d316929, d317850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315691 q = 1) (hb : d316930 q = 1) : d317851 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d315691, d316930, d317851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315691, d316930, d317851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315693 q = 1) (hb : d316932 q = 1) : d317853 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315693, d316932, d317853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83786 q ha hb
    | true =>
      simp only [d315693, d316932, d317853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d315694 q = 1) (hb : d316933 q = 1) : d317854 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315694, d316933, d317854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315694, d316933, d317854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d315695 q = 1) (hb : d316934 q = 1) : d317855 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315695, d316934, d317855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d315695, d316934, d317855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d315696 q = 1) (hb : d316935 q = 1) : d317856 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315696, d316935, d317856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315696, d316935, d317856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d315697 q = 1) (hb : d316936 q = 1) : d317857 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d315697, d316936, d317857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315697, d316936, d317857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d315698 q = 1) (hb : d316937 q = 1) : d317858 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d315698, d316937, d317858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315698, d316937, d317858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro83811 (p : Pattern) (ha : d315705 p = 1) (hb : d316944 p = 1) : d317865 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315677 q = 1) (hb : d316916 q = 1) : d317837 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315677, d316916, d317837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83806 q ha hb
    | true =>
      simp only [d315677, d316916, d317837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83785 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d315583 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d315678 q = 1) (hb : d316917 q = 1) : d317838 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315678, d316917, d317838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d315678, d316917, d317838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d315680 q = 1) (hb : d316919 q = 1) : d317840 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315680, d316919, d317840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83807 q ha hb
    | true =>
      simp only [d315680, d316919, d317840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d315681 q = 1) (hb : d316920 q = 1) : d317841 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315681, d316920, d317841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315681, d316920, d317841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d315682 q = 1) (hb : d316921 q = 1) : d317842 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315682, d316921, d317842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315682, d316921, d317842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d315703 q = 1) (hb : d316942 q = 1) : d317863 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315703, d316942, d317863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315703, d316942, d317863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d315704 q = 1) (hb : d316943 q = 1) : d317864 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d315704, d316943, d317864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315704, d316943, d317864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d315705 q = 1) (hb : d316944 q = 1) : d317865 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d315705, d316944, d317865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315705, d316944, d317865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro83812 (p : Pattern) (ha : d315707 p = 1) (hb : d316946 p = 1) : d317867 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315693 q = 1) (hb : d316932 q = 1) : d317853 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315693, d316932, d317853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83786 q ha hb
    | true =>
      simp only [d315693, d316932, d317853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315694 q = 1) (hb : d316933 q = 1) : d317854 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315694, d316933, d317854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315694, d316933, d317854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315695 q = 1) (hb : d316934 q = 1) : d317855 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315695, d316934, d317855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315695, d316934, d317855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315696 q = 1) (hb : d316935 q = 1) : d317856 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315696, d316935, d317856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315696, d316935, d317856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315697 q = 1) (hb : d316936 q = 1) : d317857 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d315697, d316936, d317857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315697, d316936, d317857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315707 q = 1) (hb : d316946 q = 1) : d317867 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d315707, d316946, d317867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315707, d316946, d317867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83813 (p : Pattern) (ha : d286853 p = 1) (hb : d315763 p = 1) : d317911 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d286829 q = 1) (hb : d315748 q = 1) : d317901 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d286829, d315748, d317901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d286829, d315748, d317901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83771 q ha hb
  have h2 (q : Pattern) (ha : d286641 q = 1) (hb : d315534 q = 1) : d317728 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d286641, d315534, d317728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83771 q ha hb
    | true =>
      simp only [d286641, d315534, d317728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d286830 q = 1) (hb : d315749 q = 1) : d317902 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d286830, d315749, d317902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286830, d315749, d317902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d286642 q = 1) (hb : d315535 q = 1) : d317729 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d286642, d315535, d317729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d286642, d315535, d317729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d286831 q = 1) (hb : d315750 q = 1) : d317903 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d286831, d315750, d317903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d286831, d315750, d317903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d286832 q = 1) (hb : d315751 q = 1) : d317904 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d286832, d315751, d317904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d286832, d315751, d317904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d286838 q = 1) (hb : d315757 q = 1) : d317910 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d286838, d315757, d317910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d286838, d315757, d317910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d315762 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d286853 q = 1) (hb : d315763 q = 1) : d317911 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d286853, d315763, d317911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d286853, d315763, d317911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro83814 (p : Pattern) (ha : d315733 p = 1) (hb : d316981 p = 1) : d317887 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315719 q = 1) (hb : d316971 q = 1) : d317873 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315719, d316971, d317873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315719, d316971, d317873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83775 q ha hb
  have h2 (q : Pattern) (ha : d315494 q = 1) (hb : d316771 q = 1) : d317699 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315494, d316771, d317699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83775 q ha hb
    | true =>
      simp only [d315494, d316771, d317699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d315720 q = 1) (hb : d316972 q = 1) : d317874 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315720, d316972, d317874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d315720, d316972, d317874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315495 q = 1) (hb : d316772 q = 1) : d317700 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315495, d316772, d317700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315495, d316772, d317700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d315721 q = 1) (hb : d316973 q = 1) : d317875 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d315721, d316973, d317875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315721, d316973, d317875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315722 q = 1) (hb : d316974 q = 1) : d317876 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d315722, d316974, d317876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315722, d316974, d317876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d315723 q = 1) (hb : d316975 q = 1) : d317877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315723, d316975, d317877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315723, d316975, d317877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83776 q ha hb
  have h8 (q : Pattern) (ha : d315503 q = 1) (hb : d316779 q = 1) : d317704 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315503, d316779, d317704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83776 q ha hb
    | true =>
      simp only [d315503, d316779, d317704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d315724 q = 1) (hb : d316976 q = 1) : d317878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315724, d316976, d317878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d315724, d316976, d317878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d315504 q = 1) (hb : d316780 q = 1) : d317705 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315504, d316780, d317705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d315504, d316780, d317705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d315725 q = 1) (hb : d316977 q = 1) : d317879 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d315725, d316977, d317879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d315725, d316977, d317879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d315726 q = 1) (hb : d316978 q = 1) : d317880 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d315726, d316978, d317880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d315726, d316978, d317880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d315727 q = 1) (hb : d316979 q = 1) : d317881 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d315727, d316979, d317881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315727, d316979, d317881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d315716 q = 1) (hb : d316968 q = 1) : d316968 q = 1 := by
    exact hb
  have h15 (q : Pattern) (ha : d286829 q = 1) (hb : d315728 q = 1) : d317882 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d286829, d315728, d317882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d286829, d315728, d317882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83773 q ha hb
  have h16 (q : Pattern) (ha : d286641 q = 1) (hb : d315518 q = 1) : d317713 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d286641, d315518, d317713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83773 q ha hb
    | true =>
      simp only [d286641, d315518, d317713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d286830 q = 1) (hb : d315729 q = 1) : d317883 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d286830, d315729, d317883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d286830, d315729, d317883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d286642 q = 1) (hb : d315519 q = 1) : d317714 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d286642, d315519, d317714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d286642, d315519, d317714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d286831 q = 1) (hb : d315730 q = 1) : d317884 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d286831, d315730, d317884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d286831, d315730, d317884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d286832 q = 1) (hb : d315731 q = 1) : d317885 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d286832, d315731, d317885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d286832, d315731, d317885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d315732 q = 1) (hb : d316980 q = 1) : d317886 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d315732, d316980, d317886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d315732, d316980, d317886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
  have h22 (q : Pattern) (ha : d315733 q = 1) (hb : d316981 q = 1) : d317887 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d315733, d316981, d317887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d315733, d316981, d317887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro83815 (p : Pattern) (ha : d315739 p = 1) (hb : d316985 p = 1) : d317892 p = 1 := by
  have h0 (q : Pattern) (ha : d315726 q = 1) (hb : d316968 q = 1) : d316968 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d286829 q = 1) (hb : d315728 q = 1) : d317882 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d286829, d315728, d317882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286829, d315728, d317882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83773 q ha hb
  have h3 (q : Pattern) (ha : d286641 q = 1) (hb : d315518 q = 1) : d317713 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d286641, d315518, d317713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83773 q ha hb
    | true =>
      simp only [d286641, d315518, d317713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d286830 q = 1) (hb : d315729 q = 1) : d317883 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d286830, d315729, d317883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d286830, d315729, d317883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d286642 q = 1) (hb : d315519 q = 1) : d317714 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d286642, d315519, d317714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d286642, d315519, d317714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d286831 q = 1) (hb : d315730 q = 1) : d317884 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d286831, d315730, d317884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d286831, d315730, d317884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d286832 q = 1) (hb : d315731 q = 1) : d317885 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d286832, d315731, d317885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d286832, d315731, d317885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d315737 q = 1) (hb : d316980 q = 1) : d317886 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d315737, d316980, d317886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d315737, d316980, d317886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d286838 q = 1) (hb : d315738 q = 1) : d317891 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d286838, d315738, d317891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d286838, d315738, d317891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d315739 q = 1) (hb : d316985 q = 1) : d317892 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d315739, d316985, d317892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d315739, d316985, d317892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro83816 (p : Pattern) (ha : d315753 p = 1) (hb : d316995 p = 1) : d317906 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315744 q = 1) (hb : d316990 q = 1) : d317897 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315744, d316990, d317897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315744, d316990, d317897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83778 q ha hb
  have h2 (q : Pattern) (ha : d315529 q = 1) (hb : d316792 q = 1) : d317723 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315529, d316792, d317723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83778 q ha hb
    | true =>
      simp only [d315529, d316792, d317723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d315745 q = 1) (hb : d316991 q = 1) : d317898 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315745, d316991, d317898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d315745, d316991, d317898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315530 q = 1) (hb : d316793 q = 1) : d317724 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315530, d316793, d317724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315530, d316793, d317724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d315746 q = 1) (hb : d316992 q = 1) : d317899 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d315746, d316992, d317899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315746, d316992, d317899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315747 q = 1) (hb : d316993 q = 1) : d317900 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d315747, d316993, d317900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315747, d316993, d317900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d286829 q = 1) (hb : d315748 q = 1) : d317901 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d286829, d315748, d317901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d286829, d315748, d317901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83771 q ha hb
  have h8 (q : Pattern) (ha : d286641 q = 1) (hb : d315534 q = 1) : d317728 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d286641, d315534, d317728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83771 q ha hb
    | true =>
      simp only [d286641, d315534, d317728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d286830 q = 1) (hb : d315749 q = 1) : d317902 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d286830, d315749, d317902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d286830, d315749, d317902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d286642 q = 1) (hb : d315535 q = 1) : d317729 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d286642, d315535, d317729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d286642, d315535, d317729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d286831 q = 1) (hb : d315750 q = 1) : d317903 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d286831, d315750, d317903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d286831, d315750, d317903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d286832 q = 1) (hb : d315751 q = 1) : d317904 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d286832, d315751, d317904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d286832, d315751, d317904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d315752 q = 1) (hb : d316994 q = 1) : d317905 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d315752, d316994, d317905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315752, d316994, d317905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d286829 q = 1) (hb : d315728 q = 1) : d317882 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d286829, d315728, d317882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d286829, d315728, d317882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83773 q ha hb
  have h15 (q : Pattern) (ha : d286641 q = 1) (hb : d315518 q = 1) : d317713 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d286641, d315518, d317713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83773 q ha hb
    | true =>
      simp only [d286641, d315518, d317713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d286830 q = 1) (hb : d315729 q = 1) : d317883 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d286830, d315729, d317883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d286830, d315729, d317883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d286642 q = 1) (hb : d315519 q = 1) : d317714 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d286642, d315519, d317714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d286642, d315519, d317714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d286831 q = 1) (hb : d315730 q = 1) : d317884 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d286831, d315730, d317884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d286831, d315730, d317884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d286832 q = 1) (hb : d315731 q = 1) : d317885 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d286832, d315731, d317885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d286832, d315731, d317885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d286838 q = 1) (hb : d315738 q = 1) : d317891 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d286838, d315738, d317891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d286838, d315738, d317891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d315753 q = 1) (hb : d316995 q = 1) : d317906 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d315753, d316995, d317906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d315753, d316995, d317906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
  exact h21 p ha hb
theorem andIntro83817 (p : Pattern) (ha : d315769 p = 1) (hb : d317004 p = 1) : d317917 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315718 q = 1) (hb : d316970 q = 1) : d316970 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d315734 q = 1) (hb : d316982 q = 1) : d317888 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315734, d316982, d317888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d315734, d316982, d317888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83814 q ha hb
  have h3 (q : Pattern) (ha : d315735 q = 1) (hb : d316983 q = 1) : d317889 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315735, d316983, d317889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315735, d316983, d317889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315736 q = 1) (hb : d316984 q = 1) : d317890 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315736, d316984, d317890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315736, d316984, d317890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315740 q = 1) (hb : d316986 q = 1) : d317893 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315740, d316986, d317893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83814 q ha hb
    | true =>
      simp only [d315740, d316986, d317893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83815 q ha hb
  have h6 (q : Pattern) (ha : d315741 q = 1) (hb : d316987 q = 1) : d317894 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315741, d316987, d317894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315741, d316987, d317894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d315742 q = 1) (hb : d316988 q = 1) : d317895 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315742, d316988, d317895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315742, d316988, d317895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d315743 q = 1) (hb : d316989 q = 1) : d317896 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d315743, d316989, d317896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315743, d316989, d317896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d315754 q = 1) (hb : d316996 q = 1) : d317907 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315754, d316996, d317907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83814 q ha hb
    | true =>
      simp only [d315754, d316996, d317907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83816 q ha hb
  have h10 (q : Pattern) (ha : d315755 q = 1) (hb : d316997 q = 1) : d317908 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315755, d316997, d317908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315755, d316997, d317908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d315756 q = 1) (hb : d316998 q = 1) : d317909 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315756, d316998, d317909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315756, d316998, d317909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d315764 q = 1) (hb : d316999 q = 1) : d317912 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315764, d316999, d317912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83816 q ha hb
    | true =>
      simp only [d315764, d316999, d317912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83813 q hb ha
  have h13 (q : Pattern) (ha : d315765 q = 1) (hb : d317000 q = 1) : d317913 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315765, d317000, d317913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315765, d317000, d317913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d315766 q = 1) (hb : d317001 q = 1) : d317914 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315766, d317001, d317914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315766, d317001, d317914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d315767 q = 1) (hb : d317002 q = 1) : d317915 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d315767, d317002, d317915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d315767, d317002, d317915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d315768 q = 1) (hb : d317003 q = 1) : d317916 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d315768, d317003, d317916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d315768, d317003, d317916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d315769 q = 1) (hb : d317004 q = 1) : d317917 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d315769, d317004, d317917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d315769, d317004, d317917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h17 p ha hb
theorem andIntro83818 (p : Pattern) (ha : d315774 p = 1) (hb : d317009 p = 1) : d317922 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315754 q = 1) (hb : d316996 q = 1) : d317907 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315754, d316996, d317907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83814 q ha hb
    | true =>
      simp only [d315754, d316996, d317907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83816 q ha hb
  have h2 (q : Pattern) (ha : d315755 q = 1) (hb : d316997 q = 1) : d317908 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315755, d316997, d317908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315755, d316997, d317908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315756 q = 1) (hb : d316998 q = 1) : d317909 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315756, d316998, d317909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315756, d316998, d317909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315764 q = 1) (hb : d316999 q = 1) : d317912 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315764, d316999, d317912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83816 q ha hb
    | true =>
      simp only [d315764, d316999, d317912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83813 q hb ha
  have h5 (q : Pattern) (ha : d315765 q = 1) (hb : d317000 q = 1) : d317913 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315765, d317000, d317913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315765, d317000, d317913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315766 q = 1) (hb : d317001 q = 1) : d317914 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315766, d317001, d317914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315766, d317001, d317914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d315767 q = 1) (hb : d317002 q = 1) : d317915 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d315767, d317002, d317915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315767, d317002, d317915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d315772 q = 1) (hb : d317007 q = 1) : d317920 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d315772, d317007, d317920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315772, d317007, d317920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d315773 q = 1) (hb : d317008 q = 1) : d317921 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d315773, d317008, d317921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d315773, d317008, d317921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d315774 q = 1) (hb : d317009 q = 1) : d317922 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d315774, d317009, d317922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d315774, d317009, d317922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro83819 (p : Pattern) (ha : d315780 p = 1) (hb : d317015 p = 1) : d317928 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315770 q = 1) (hb : d317005 q = 1) : d317918 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315770, d317005, d317918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83817 q ha hb
    | true =>
      simp only [d315770, d317005, d317918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315771 q = 1) (hb : d317006 q = 1) : d317919 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315771, d317006, d317919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315771, d317006, d317919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315775 q = 1) (hb : d317010 q = 1) : d317923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315775, d317010, d317923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83818 q ha hb
    | true =>
      simp only [d315775, d317010, d317923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315776 q = 1) (hb : d317011 q = 1) : d317924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315776, d317011, d317924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315776, d317011, d317924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315777 q = 1) (hb : d317012 q = 1) : d317925 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315777, d317012, d317925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315777, d317012, d317925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315778 q = 1) (hb : d317013 q = 1) : d317926 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315778, d317013, d317926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315778, d317013, d317926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d315779 q = 1) (hb : d317014 q = 1) : d317927 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315779, d317014, d317927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315779, d317014, d317927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d315780 q = 1) (hb : d317015 q = 1) : d317928 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315780, d317015, d317928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d315780, d317015, d317928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro83820 (p : Pattern) (ha : d315782 p = 1) (hb : d317017 p = 1) : d317930 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315764 q = 1) (hb : d316999 q = 1) : d317912 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315764, d316999, d317912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83816 q ha hb
    | true =>
      simp only [d315764, d316999, d317912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83813 q hb ha
  have h2 (q : Pattern) (ha : d315765 q = 1) (hb : d317000 q = 1) : d317913 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315765, d317000, d317913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315765, d317000, d317913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315766 q = 1) (hb : d317001 q = 1) : d317914 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315766, d317001, d317914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315766, d317001, d317914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315772 q = 1) (hb : d317007 q = 1) : d317920 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d315772, d317007, d317920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315772, d317007, d317920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d315781 q = 1) (hb : d317016 q = 1) : d317929 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d315781, d317016, d317929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315781, d317016, d317929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d315782 q = 1) (hb : d317017 q = 1) : d317930 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d315782, d317017, d317930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315782, d317017, d317930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83821 (p : Pattern) (ha : d315788 p = 1) (hb : d317023 p = 1) : d317936 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315775 q = 1) (hb : d317010 q = 1) : d317923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315775, d317010, d317923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83818 q ha hb
    | true =>
      simp only [d315775, d317010, d317923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315776 q = 1) (hb : d317011 q = 1) : d317924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315776, d317011, d317924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315776, d317011, d317924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315783 q = 1) (hb : d317018 q = 1) : d317931 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315783, d317018, d317931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83820 q ha hb
    | true =>
      simp only [d315783, d317018, d317931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315784 q = 1) (hb : d317019 q = 1) : d317932 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315784, d317019, d317932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315784, d317019, d317932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315785 q = 1) (hb : d317020 q = 1) : d317933 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315785, d317020, d317933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315785, d317020, d317933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315786 q = 1) (hb : d317021 q = 1) : d317934 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315786, d317021, d317934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315786, d317021, d317934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d315787 q = 1) (hb : d317022 q = 1) : d317935 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315787, d317022, d317935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315787, d317022, d317935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d315788 q = 1) (hb : d317023 q = 1) : d317936 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315788, d317023, d317936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d315788, d317023, d317936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro83822 (p : Pattern) (ha : d286853 p = 1) (hb : d315807 p = 1) : d317911 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d286829 q = 1) (hb : d315802 q = 1) : d317901 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d286829, d315802, d317901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d286829, d315802, d317901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83795 q ha hb
  have h2 (q : Pattern) (ha : d286641 q = 1) (hb : d315641 q = 1) : d317728 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d286641, d315641, d317728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83795 q ha hb
    | true =>
      simp only [d286641, d315641, d317728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d286830 q = 1) (hb : d315803 q = 1) : d317902 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d286830, d315803, d317902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286830, d315803, d317902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d286642 q = 1) (hb : d315642 q = 1) : d317729 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d286642, d315642, d317729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d286642, d315642, d317729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d286831 q = 1) (hb : d315804 q = 1) : d317903 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d286831, d315804, d317903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d286831, d315804, d317903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d286832 q = 1) (hb : d315805 q = 1) : d317904 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d286832, d315805, d317904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d286832, d315805, d317904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d286838 q = 1) (hb : d315806 q = 1) : d317910 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d286838, d315806, d317910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d286838, d315806, d317910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d286853 q = 1) (hb : d315807 q = 1) : d317911 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d286853, d315807, d317911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d286853, d315807, d317911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro83823 (p : Pattern) (ha : d315801 p = 1) (hb : d316995 p = 1) : d317906 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315744 q = 1) (hb : d316990 q = 1) : d317897 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315744, d316990, d317897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315744, d316990, d317897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83778 q ha hb
  have h2 (q : Pattern) (ha : d315529 q = 1) (hb : d316792 q = 1) : d317723 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315529, d316792, d317723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83778 q ha hb
    | true =>
      simp only [d315529, d316792, d317723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d315745 q = 1) (hb : d316991 q = 1) : d317898 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315745, d316991, d317898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d315745, d316991, d317898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315530 q = 1) (hb : d316793 q = 1) : d317724 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315530, d316793, d317724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315530, d316793, d317724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d315746 q = 1) (hb : d316992 q = 1) : d317899 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d315746, d316992, d317899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315746, d316992, d317899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315747 q = 1) (hb : d316993 q = 1) : d317900 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d315747, d316993, d317900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315747, d316993, d317900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d286829 q = 1) (hb : d315748 q = 1) : d317901 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d286829, d315748, d317901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d286829, d315748, d317901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83771 q ha hb
  have h8 (q : Pattern) (ha : d286641 q = 1) (hb : d315534 q = 1) : d317728 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d286641, d315534, d317728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83771 q ha hb
    | true =>
      simp only [d286641, d315534, d317728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d286830 q = 1) (hb : d315749 q = 1) : d317902 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d286830, d315749, d317902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d286830, d315749, d317902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d286642 q = 1) (hb : d315535 q = 1) : d317729 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d286642, d315535, d317729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d286642, d315535, d317729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d286831 q = 1) (hb : d315750 q = 1) : d317903 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d286831, d315750, d317903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d286831, d315750, d317903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d286832 q = 1) (hb : d315751 q = 1) : d317904 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d286832, d315751, d317904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d286832, d315751, d317904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d315752 q = 1) (hb : d316994 q = 1) : d317905 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d315752, d316994, d317905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315752, d316994, d317905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d286829 q = 1) (hb : d315796 q = 1) : d317882 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d286829, d315796, d317882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d286829, d315796, d317882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83797 q ha hb
  have h15 (q : Pattern) (ha : d286641 q = 1) (hb : d315634 q = 1) : d317713 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d286641, d315634, d317713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83797 q ha hb
    | true =>
      simp only [d286641, d315634, d317713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d286830 q = 1) (hb : d315797 q = 1) : d317883 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d286830, d315797, d317883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d286830, d315797, d317883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d286642 q = 1) (hb : d315635 q = 1) : d317714 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d286642, d315635, d317714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d286642, d315635, d317714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d286831 q = 1) (hb : d315798 q = 1) : d317884 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d286831, d315798, d317884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d286831, d315798, d317884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d286832 q = 1) (hb : d315799 q = 1) : d317885 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d286832, d315799, d317885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d286832, d315799, d317885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d286838 q = 1) (hb : d315800 q = 1) : d317891 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d286838, d315800, d317891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d286838, d315800, d317891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d315801 q = 1) (hb : d316995 q = 1) : d317906 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d315801, d316995, d317906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d315801, d316995, d317906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
  exact h21 p ha hb
theorem andIntro83824 (p : Pattern) (ha : d315813 p = 1) (hb : d317009 p = 1) : d317922 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315754 q = 1) (hb : d316996 q = 1) : d317907 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315754, d316996, d317907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83814 q ha hb
    | true =>
      simp only [d315754, d316996, d317907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83816 q ha hb
  have h2 (q : Pattern) (ha : d315755 q = 1) (hb : d316997 q = 1) : d317908 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315755, d316997, d317908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315755, d316997, d317908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315756 q = 1) (hb : d316998 q = 1) : d317909 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315756, d316998, d317909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315756, d316998, d317909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315764 q = 1) (hb : d316999 q = 1) : d317912 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315764, d316999, d317912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83816 q ha hb
    | true =>
      simp only [d315764, d316999, d317912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83813 q hb ha
  have h5 (q : Pattern) (ha : d315765 q = 1) (hb : d317000 q = 1) : d317913 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315765, d317000, d317913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315765, d317000, d317913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315766 q = 1) (hb : d317001 q = 1) : d317914 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315766, d317001, d317914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315766, d317001, d317914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d315767 q = 1) (hb : d317002 q = 1) : d317915 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d315767, d317002, d317915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315767, d317002, d317915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d315808 q = 1) (hb : d316999 q = 1) : d317912 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315808, d316999, d317912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83823 q ha hb
    | true =>
      simp only [d315808, d316999, d317912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83822 q hb ha
  have h9 (q : Pattern) (ha : d315809 q = 1) (hb : d317000 q = 1) : d317913 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315809, d317000, d317913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315809, d317000, d317913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d315810 q = 1) (hb : d317001 q = 1) : d317914 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315810, d317001, d317914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315810, d317001, d317914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d315811 q = 1) (hb : d317007 q = 1) : d317920 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d315811, d317007, d317920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d315811, d317007, d317920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d315812 q = 1) (hb : d317008 q = 1) : d317921 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d315812, d317008, d317921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d315812, d317008, d317921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d315813 q = 1) (hb : d317009 q = 1) : d317922 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d315813, d317009, d317922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d315813, d317009, d317922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro83825 (p : Pattern) (ha : d315819 p = 1) (hb : d317029 p = 1) : d317942 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315814 q = 1) (hb : d317010 q = 1) : d317923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315814, d317010, d317923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83824 q ha hb
    | true =>
      simp only [d315814, d317010, d317923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315815 q = 1) (hb : d317011 q = 1) : d317924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315815, d317011, d317924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315815, d317011, d317924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315816 q = 1) (hb : d317026 q = 1) : d317939 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315816, d317026, d317939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315816, d317026, d317939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315817 q = 1) (hb : d317027 q = 1) : d317940 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315817, d317027, d317940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315817, d317027, d317940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d315818 q = 1) (hb : d317028 q = 1) : d317941 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315818, d317028, d317941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315818, d317028, d317941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d315819 q = 1) (hb : d317029 q = 1) : d317942 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315819, d317029, d317942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315819, d317029, d317942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83826 (p : Pattern) (ha : d315825 p = 1) (hb : d317035 p = 1) : d317948 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315789 q = 1) (hb : d317024 q = 1) : d317937 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315789, d317024, d317937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83819 q ha hb
    | true =>
      simp only [d315789, d317024, d317937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83821 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d315794 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d315795 q = 1) (hb : d317025 q = 1) : d317938 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315795, d317025, d317938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d315795, d317025, d317938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d315820 q = 1) (hb : d317030 q = 1) : d317943 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315820, d317030, d317943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83825 q ha hb
    | true =>
      simp only [d315820, d317030, d317943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d315821 q = 1) (hb : d317031 q = 1) : d317944 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315821, d317031, d317944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315821, d317031, d317944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d315822 q = 1) (hb : d317032 q = 1) : d317945 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315822, d317032, d317945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315822, d317032, d317945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d315823 q = 1) (hb : d317033 q = 1) : d317946 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315823, d317033, d317946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315823, d317033, d317946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d315824 q = 1) (hb : d317034 q = 1) : d317947 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d315824, d317034, d317947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315824, d317034, d317947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d315825 q = 1) (hb : d317035 q = 1) : d317948 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d315825, d317035, d317948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315825, d317035, d317948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro83827 (p : Pattern) (ha : d315793 p = 1) (hb : d317040 p = 1) : d317953 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315783 q = 1) (hb : d317018 q = 1) : d317931 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315783, d317018, d317931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83820 q ha hb
    | true =>
      simp only [d315783, d317018, d317931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315784 q = 1) (hb : d317019 q = 1) : d317932 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315784, d317019, d317932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315784, d317019, d317932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315790 q = 1) (hb : d317037 q = 1) : d317950 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315790, d317037, d317950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315790, d317037, d317950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315791 q = 1) (hb : d317038 q = 1) : d317951 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315791, d317038, d317951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315791, d317038, d317951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d315792 q = 1) (hb : d317039 q = 1) : d317952 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315792, d317039, d317952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315792, d317039, d317952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d315793 q = 1) (hb : d317040 q = 1) : d317953 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315793, d317040, d317953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315793, d317040, d317953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83828 (p : Pattern) (ha : d315832 p = 1) (hb : d317046 p = 1) : d317959 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315827 q = 1) (hb : d317041 q = 1) : d317954 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315827, d317041, d317954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83827 q ha hb
    | true =>
      simp only [d315827, d317041, d317954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315828 q = 1) (hb : d317042 q = 1) : d317955 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315828, d317042, d317955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315828, d317042, d317955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315829 q = 1) (hb : d317043 q = 1) : d317956 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315829, d317043, d317956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315829, d317043, d317956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315830 q = 1) (hb : d317044 q = 1) : d317957 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315830, d317044, d317957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315830, d317044, d317957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315831 q = 1) (hb : d317045 q = 1) : d317958 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d315831, d317045, d317958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315831, d317045, d317958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315832 q = 1) (hb : d317046 q = 1) : d317959 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d315832, d317046, d317959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315832, d317046, d317959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83829 (p : Pattern) (ha : d315838 p = 1) (hb : d317052 p = 1) : d317965 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315579 q = 1) (hb : d316828 q = 1) : d317767 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d315579, d316828, d317767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315579, d316828, d317767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83784 q ha hb
  have h2 (q : Pattern) (ha : d315580 q = 1) (hb : d316829 q = 1) : d317768 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d315580, d316829, d317768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d315580, d316829, d317768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d315589 q = 1) (hb : d316838 q = 1) : d317777 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d315589, d316838, d317777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83784 q ha hb
    | true =>
      simp only [d315589, d316838, d317777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83787 q ha hb
  have h4 (q : Pattern) (ha : d315590 q = 1) (hb : d316839 q = 1) : d317778 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d315590, d316839, d317778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315590, d316839, d317778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d315591 q = 1) (hb : d316840 q = 1) : d317779 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d315591, d316840, d317779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315591, d316840, d317779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315686 q = 1) (hb : d316925 q = 1) : d317846 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d315686, d316925, d317846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83801 q ha hb
    | true =>
      simp only [d315686, d316925, d317846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83808 q ha hb
  have h7 (q : Pattern) (ha : d315699 q = 1) (hb : d316938 q = 1) : d317859 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d315699, d316938, d317859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83809 q ha hb
    | true =>
      simp only [d315699, d316938, d317859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83810 q ha hb
  have h8 (q : Pattern) (ha : d315700 q = 1) (hb : d316939 q = 1) : d317860 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d315700, d316939, d317860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315700, d316939, d317860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d315701 q = 1) (hb : d316940 q = 1) : d317861 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d315701, d316940, d317861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d315701, d316940, d317861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d315702 q = 1) (hb : d316941 q = 1) : d317862 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d315702, d316941, d317862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315702, d316941, d317862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d315706 q = 1) (hb : d316945 q = 1) : d317866 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d315706, d316945, d317866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315706, d316945, d317866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83811 q ha hb
  have h12 (q : Pattern) (ha : d315708 q = 1) (hb : d316947 q = 1) : d317868 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d315708, d316947, d317868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315708, d316947, d317868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83812 q ha hb
  have h13 (q : Pattern) (ha : d315709 q = 1) (hb : d316948 q = 1) : d317869 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d315709, d316948, d317869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d315709, d316948, d317869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d315710 q = 1) (hb : d316949 q = 1) : d317870 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d315710, d316949, d317870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d315710, d316949, d317870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d315711 q = 1) (hb : d316950 q = 1) : d317871 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d315711, d316950, d317871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d315711, d316950, d317871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d315712 q = 1) (hb : d316951 q = 1) : d317872 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d315712, d316951, d317872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d315712, d316951, d317872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d315826 q = 1) (hb : d317036 q = 1) : d317949 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d315826, d317036, d317949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315826, d317036, d317949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83826 q ha hb
  have h18 (q : Pattern) (ha : d315833 q = 1) (hb : d317047 q = 1) : d317960 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d315833, d317047, d317960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315833, d317047, d317960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83828 q ha hb
  have h19 (q : Pattern) (ha : d315834 q = 1) (hb : d317048 q = 1) : d317961 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d315834, d317048, d317961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d315834, d317048, d317961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d315835 q = 1) (hb : d317049 q = 1) : d317962 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d315835, d317049, d317962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d315835, d317049, d317962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d315836 q = 1) (hb : d317050 q = 1) : d317963 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d315836, d317050, d317963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d315836, d317050, d317963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d315837 q = 1) (hb : d317051 q = 1) : d317964 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d315837, d317051, d317964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d315837, d317051, d317964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d315838 q = 1) (hb : d317052 q = 1) : d317965 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d315838, d317052, d317965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d315838, d317052, d317965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro83830 (p : Pattern) (ha : d315844 p = 1) (hb : d317058 p = 1) : d317971 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315839 q = 1) (hb : d317053 q = 1) : d317966 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d315839, d317053, d317966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315839, d317053, d317966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83829 q ha hb
  have h2 (q : Pattern) (ha : d315840 q = 1) (hb : d317054 q = 1) : d317967 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d315840, d317054, d317967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315840, d317054, d317967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315841 q = 1) (hb : d317055 q = 1) : d317968 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d315841, d317055, d317968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315841, d317055, d317968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315842 q = 1) (hb : d317056 q = 1) : d317969 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d315842, d317056, d317969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315842, d317056, d317969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315843 q = 1) (hb : d317057 q = 1) : d317970 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d315843, d317057, d317970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315843, d317057, d317970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315844 q = 1) (hb : d317058 q = 1) : d317971 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d315844, d317058, d317971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315844, d317058, d317971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83831 (p : Pattern) (ha : d2028 p = 1) (hb : d53306 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307 q = 1) (hb : d52106 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307, d52106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1997 q = 1) (hb : d53276 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1997, d53276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1997, d53276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d2013 q = 1) (hb : d53292 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2013, d53292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2013, d53292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d2027 q = 1) (hb : d53306 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2027, d53306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2027, d53306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d2028 q = 1) (hb : d53306 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d2028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro83832 (p : Pattern) (ha : d315874 p = 1) (hb : d317079 p = 1) : d317976 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d317064 q = 1) : d317064 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d315849 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53306 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2029 q = 1) (hb : d53306 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83831 q ha hb
    | true =>
      simp only [d2029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2030 q = 1) (hb : d315870 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2030, d315870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2030, d315870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2031 q = 1) (hb : d315871 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2031, d315871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2031, d315871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d27032 q = 1) : d27032 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d315872 q = 1) (hb : d317077 q = 1) : d235783 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d315872, d317077, d235783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d315872, d317077, d235783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d315873 q = 1) (hb : d317078 q = 1) : d235784 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d315873, d317078, d235784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d315873, d317078, d235784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d315874 q = 1) (hb : d317079 q = 1) : d317976 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d315874, d317079, d317976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d315874, d317079, d317976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro83833 (p : Pattern) (ha : d315879 p = 1) (hb : d317084 p = 1) : d317094 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d315849 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53306 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2029 q = 1) (hb : d53306 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83831 q ha hb
    | true =>
      simp only [d2029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2030 q = 1) (hb : d315870 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2030, d315870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2030, d315870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2031 q = 1) (hb : d315871 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2031, d315871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2031, d315871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d27032 q = 1) : d27032 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d315872 q = 1) (hb : d317077 q = 1) : d235783 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d315872, d317077, d235783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d315872, d317077, d235783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d315873 q = 1) (hb : d317078 q = 1) : d235784 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d315873, d317078, d235784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d315873, d317078, d235784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d315862 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d315879 q = 1) (hb : d317084 q = 1) : d317094 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d315879, d317084, d317094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d315879, d317084, d317094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro83834 (p : Pattern) (ha : d315886 p = 1) (hb : d317090 p = 1) : d317982 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315875 q = 1) (hb : d317080 q = 1) : d317977 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315875, d317080, d317977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83832 q ha hb
    | true =>
      simp only [d315875, d317080, d317977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315876 q = 1) (hb : d317081 q = 1) : d317978 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315876, d317081, d317978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d315876, d317081, d317978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d315877 q = 1) (hb : d317082 q = 1) : d317979 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d315877, d317082, d317979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315877, d317082, d317979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315878 q = 1) (hb : d317083 q = 1) : d317980 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d315878, d317083, d317980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315878, d317083, d317980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d315880 q = 1) (hb : d317085 q = 1) : d317095 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315880, d317085, d317095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83833 q ha hb
    | true =>
      simp only [d315880, d317085, d317095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d315881 q = 1) (hb : d317086 q = 1) : d317096 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315881, d317086, d317096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315881, d317086, d317096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d315882 q = 1) (hb : d317087 q = 1) : d317097 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d315882, d317087, d317097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315882, d317087, d317097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d315883 q = 1) (hb : d317088 q = 1) : d317098 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d315883, d317088, d317098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d315883, d317088, d317098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d315884 q = 1) (hb : d317089 q = 1) : d317981 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d315884, d317089, d317981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315884, d317089, d317981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d315885 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d315886 q = 1) (hb : d317090 q = 1) : d317982 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d315886, d317090, d317982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d315886, d317090, d317982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro83835 (p : Pattern) (ha : d315897 p = 1) (hb : d317106 p = 1) : d317100 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315880 q = 1) (hb : d317085 q = 1) : d317095 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315880, d317085, d317095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83833 q ha hb
    | true =>
      simp only [d315880, d317085, d317095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315881 q = 1) (hb : d317086 q = 1) : d317096 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315881, d317086, d317096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d315881, d317086, d317096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d315882 q = 1) (hb : d317087 q = 1) : d317097 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d315882, d317087, d317097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315882, d317087, d317097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315883 q = 1) (hb : d317088 q = 1) : d317098 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d315883, d317088, d317098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315883, d317088, d317098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d315890 q = 1) (hb : d317105 q = 1) : d317099 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d315890, d317105, d317099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315890, d317105, d317099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d315896 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d315897 q = 1) (hb : d317106 q = 1) : d317100 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d315897, d317106, d317100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315897, d317106, d317100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro83836 (p : Pattern) (ha : d315904 p = 1) (hb : d317112 p = 1) : d317992 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315869 q = 1) (hb : d317076 q = 1) : d317076 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d315887 q = 1) (hb : d317091 q = 1) : d317983 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315887, d317091, d317983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d315887, d317091, d317983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83834 q ha hb
  have h3 (q : Pattern) (ha : d315888 q = 1) (hb : d317092 q = 1) : d317984 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315888, d317092, d317984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315888, d317092, d317984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315889 q = 1) (hb : d317093 q = 1) : d317985 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315889, d317093, d317985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315889, d317093, d317985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315897 q = 1) (hb : d317100 q = 1) : d317100 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d315898 q = 1) (hb : d317101 q = 1) : d317986 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315898, d317101, d317986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83834 q ha hb
    | true =>
      simp only [d315898, d317101, d317986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d315899 q = 1) (hb : d317102 q = 1) : d317987 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315899, d317102, d317987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315899, d317102, d317987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d315900 q = 1) (hb : d317103 q = 1) : d317988 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315900, d317103, d317988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315900, d317103, d317988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d315901 q = 1) (hb : d317104 q = 1) : d317989 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d315901, d317104, d317989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315901, d317104, d317989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d315898 q = 1) (hb : d317107 q = 1) : d317986 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315898, d317107, d317986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83834 q ha hb
    | true =>
      simp only [d315898, d317107, d317986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83835 q ha hb
  have h11 (q : Pattern) (ha : d315899 q = 1) (hb : d317108 q = 1) : d317987 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315899, d317108, d317987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315899, d317108, d317987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d315900 q = 1) (hb : d317109 q = 1) : d317988 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315900, d317109, d317988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315900, d317109, d317988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d315902 q = 1) (hb : d317110 q = 1) : d317990 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d315902, d317110, d317990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d315902, d317110, d317990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d315903 q = 1) (hb : d317111 q = 1) : d317991 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d315903, d317111, d317991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d315903, d317111, d317991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d315904 q = 1) (hb : d317112 q = 1) : d317992 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d315904, d317112, d317992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d315904, d317112, d317992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h15 p ha hb
theorem andIntro83837 (p : Pattern) (ha : d315908 p = 1) (hb : d317116 p = 1) : d317996 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315898 q = 1) (hb : d317107 q = 1) : d317986 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315898, d317107, d317986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83834 q ha hb
    | true =>
      simp only [d315898, d317107, d317986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83835 q ha hb
  have h2 (q : Pattern) (ha : d315899 q = 1) (hb : d317108 q = 1) : d317987 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315899, d317108, d317987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315899, d317108, d317987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315900 q = 1) (hb : d317109 q = 1) : d317988 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315900, d317109, d317988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315900, d317109, d317988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315902 q = 1) (hb : d317110 q = 1) : d317990 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d315902, d317110, d317990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315902, d317110, d317990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d315907 q = 1) (hb : d317115 q = 1) : d317995 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d315907, d317115, d317995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315907, d317115, d317995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d315908 q = 1) (hb : d317116 q = 1) : d317996 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d315908, d317116, d317996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315908, d317116, d317996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83838 (p : Pattern) (ha : d315914 p = 1) (hb : d317122 p = 1) : d318002 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315905 q = 1) (hb : d317113 q = 1) : d317993 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315905, d317113, d317993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83836 q ha hb
    | true =>
      simp only [d315905, d317113, d317993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315906 q = 1) (hb : d317114 q = 1) : d317994 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315906, d317114, d317994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315906, d317114, d317994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315909 q = 1) (hb : d317117 q = 1) : d317997 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315909, d317117, d317997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83837 q ha hb
    | true =>
      simp only [d315909, d317117, d317997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315910 q = 1) (hb : d317118 q = 1) : d317998 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315910, d317118, d317998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315910, d317118, d317998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315911 q = 1) (hb : d317119 q = 1) : d317999 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315911, d317119, d317999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315911, d317119, d317999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315912 q = 1) (hb : d317120 q = 1) : d318000 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315912, d317120, d318000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315912, d317120, d318000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d315913 q = 1) (hb : d317121 q = 1) : d318001 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315913, d317121, d318001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315913, d317121, d318001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d315914 q = 1) (hb : d317122 q = 1) : d318002 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315914, d317122, d318002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315914, d317122, d318002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83839 (p : Pattern) (ha : d315918 p = 1) (hb : d317126 p = 1) : d318006 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315909 q = 1) (hb : d317117 q = 1) : d317997 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315909, d317117, d317997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83837 q ha hb
    | true =>
      simp only [d315909, d317117, d317997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315910 q = 1) (hb : d317118 q = 1) : d317998 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315910, d317118, d317998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315910, d317118, d317998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315915 q = 1) (hb : d317123 q = 1) : d318003 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315915, d317123, d318003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315915, d317123, d318003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315916 q = 1) (hb : d317124 q = 1) : d318004 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315916, d317124, d318004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315916, d317124, d318004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d315917 q = 1) (hb : d317125 q = 1) : d318005 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315917, d317125, d318005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315917, d317125, d318005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d315918 q = 1) (hb : d317126 q = 1) : d318006 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315918, d317126, d318006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315918, d317126, d318006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83840 (p : Pattern) (ha : d315924 p = 1) (hb : d317132 p = 1) : d318012 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315919 q = 1) (hb : d317127 q = 1) : d318007 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315919, d317127, d318007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83838 q ha hb
    | true =>
      simp only [d315919, d317127, d318007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83839 q ha hb
  have h2 (q : Pattern) (ha : d315920 q = 1) (hb : d317128 q = 1) : d318008 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315920, d317128, d318008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315920, d317128, d318008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315921 q = 1) (hb : d317129 q = 1) : d318009 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315921, d317129, d318009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315921, d317129, d318009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315922 q = 1) (hb : d317130 q = 1) : d318010 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315922, d317130, d318010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315922, d317130, d318010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315923 q = 1) (hb : d317131 q = 1) : d318011 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d315923, d317131, d318011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315923, d317131, d318011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315924 q = 1) (hb : d317132 q = 1) : d318012 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d315924, d317132, d318012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315924, d317132, d318012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83841 (p : Pattern) (ha : d315927 p = 1) (hb : d317135 p = 1) : d318015 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315905 q = 1) (hb : d317113 q = 1) : d317993 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315905, d317113, d317993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83836 q ha hb
    | true =>
      simp only [d315905, d317113, d317993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315906 q = 1) (hb : d317114 q = 1) : d317994 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315906, d317114, d317994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315906, d317114, d317994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315909 q = 1) (hb : d317117 q = 1) : d317997 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315909, d317117, d317997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83837 q ha hb
    | true =>
      simp only [d315909, d317117, d317997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315910 q = 1) (hb : d317118 q = 1) : d317998 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315910, d317118, d317998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315910, d317118, d317998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315911 q = 1) (hb : d317119 q = 1) : d317999 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315911, d317119, d317999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315911, d317119, d317999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315912 q = 1) (hb : d317120 q = 1) : d318000 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315912, d317120, d318000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315912, d317120, d318000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d315913 q = 1) (hb : d317121 q = 1) : d318001 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315913, d317121, d318001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315913, d317121, d318001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d315927 q = 1) (hb : d317135 q = 1) : d318015 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315927, d317135, d318015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d315927, d317135, d318015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro83842 (p : Pattern) (ha : d315928 p = 1) (hb : d317136 p = 1) : d318016 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315909 q = 1) (hb : d317117 q = 1) : d317997 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315909, d317117, d317997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83837 q ha hb
    | true =>
      simp only [d315909, d317117, d317997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315910 q = 1) (hb : d317118 q = 1) : d317998 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315910, d317118, d317998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315910, d317118, d317998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315915 q = 1) (hb : d317123 q = 1) : d318003 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315915, d317123, d318003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315915, d317123, d318003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315916 q = 1) (hb : d317124 q = 1) : d318004 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315916, d317124, d318004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315916, d317124, d318004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d315917 q = 1) (hb : d317125 q = 1) : d318005 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315917, d317125, d318005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315917, d317125, d318005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d315928 q = 1) (hb : d317136 q = 1) : d318016 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315928, d317136, d318016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315928, d317136, d318016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83843 (p : Pattern) (ha : d315934 p = 1) (hb : d317142 p = 1) : d318022 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315919 q = 1) (hb : d317127 q = 1) : d318007 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315919, d317127, d318007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83838 q ha hb
    | true =>
      simp only [d315919, d317127, d318007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83839 q ha hb
  have h2 (q : Pattern) (ha : d315920 q = 1) (hb : d317128 q = 1) : d318008 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315920, d317128, d318008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315920, d317128, d318008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315921 q = 1) (hb : d317129 q = 1) : d318009 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315921, d317129, d318009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315921, d317129, d318009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315922 q = 1) (hb : d317130 q = 1) : d318010 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315922, d317130, d318010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315922, d317130, d318010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315923 q = 1) (hb : d317131 q = 1) : d318011 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d315923, d317131, d318011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315923, d317131, d318011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315929 q = 1) (hb : d317137 q = 1) : d318017 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315929, d317137, d318017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83841 q ha hb
    | true =>
      simp only [d315929, d317137, d318017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83842 q ha hb
  have h7 (q : Pattern) (ha : d315930 q = 1) (hb : d317138 q = 1) : d318018 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315930, d317138, d318018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315930, d317138, d318018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d315931 q = 1) (hb : d317139 q = 1) : d318019 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315931, d317139, d318019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d315931, d317139, d318019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d315932 q = 1) (hb : d317140 q = 1) : d318020 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315932, d317140, d318020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315932, d317140, d318020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d315933 q = 1) (hb : d317141 q = 1) : d318021 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d315933, d317141, d318021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315933, d317141, d318021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d315934 q = 1) (hb : d317142 q = 1) : d318022 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d315934, d317142, d318022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315934, d317142, d318022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro83844 (p : Pattern) (ha : d315904 p = 1) (hb : d317176 p = 1) : d317992 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315869 q = 1) (hb : d317076 q = 1) : d317076 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d315887 q = 1) (hb : d317091 q = 1) : d317983 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315887, d317091, d317983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d315887, d317091, d317983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83834 q ha hb
  have h3 (q : Pattern) (ha : d315888 q = 1) (hb : d317092 q = 1) : d317984 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315888, d317092, d317984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315888, d317092, d317984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315889 q = 1) (hb : d317093 q = 1) : d317985 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315889, d317093, d317985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315889, d317093, d317985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315897 q = 1) (hb : d317100 q = 1) : d317100 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d315898 q = 1) (hb : d317101 q = 1) : d317986 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315898, d317101, d317986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83834 q ha hb
    | true =>
      simp only [d315898, d317101, d317986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d315899 q = 1) (hb : d317102 q = 1) : d317987 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315899, d317102, d317987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315899, d317102, d317987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d315900 q = 1) (hb : d317103 q = 1) : d317988 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315900, d317103, d317988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315900, d317103, d317988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d315901 q = 1) (hb : d317104 q = 1) : d317989 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d315901, d317104, d317989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315901, d317104, d317989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d315902 q = 1) (hb : d317174 q = 1) : d317990 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d315902, d317174, d317990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d315902, d317174, d317990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d315903 q = 1) (hb : d317175 q = 1) : d317991 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d315903, d317175, d317991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d315903, d317175, d317991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d315904 q = 1) (hb : d317176 q = 1) : d317992 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d315904, d317176, d317992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d315904, d317176, d317992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro83845 (p : Pattern) (ha : d315914 p = 1) (hb : d317186 p = 1) : d318002 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315905 q = 1) (hb : d317177 q = 1) : d317993 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315905, d317177, d317993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83844 q ha hb
    | true =>
      simp only [d315905, d317177, d317993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315906 q = 1) (hb : d317178 q = 1) : d317994 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315906, d317178, d317994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315906, d317178, d317994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315909 q = 1) (hb : d317117 q = 1) : d317997 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315909, d317117, d317997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83837 q ha hb
    | true =>
      simp only [d315909, d317117, d317997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315910 q = 1) (hb : d317118 q = 1) : d317998 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315910, d317118, d317998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315910, d317118, d317998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315911 q = 1) (hb : d317183 q = 1) : d317999 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315911, d317183, d317999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315911, d317183, d317999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315912 q = 1) (hb : d317184 q = 1) : d318000 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315912, d317184, d318000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315912, d317184, d318000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d315913 q = 1) (hb : d317185 q = 1) : d318001 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315913, d317185, d318001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315913, d317185, d318001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d315914 q = 1) (hb : d317186 q = 1) : d318002 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315914, d317186, d318002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315914, d317186, d318002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83846 (p : Pattern) (ha : d315939 p = 1) (hb : d317147 p = 1) : d318027 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315905 q = 1) (hb : d317113 q = 1) : d317993 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315905, d317113, d317993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83836 q ha hb
    | true =>
      simp only [d315905, d317113, d317993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315906 q = 1) (hb : d317114 q = 1) : d317994 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315906, d317114, d317994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315906, d317114, d317994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315909 q = 1) (hb : d317117 q = 1) : d317997 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315909, d317117, d317997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83837 q ha hb
    | true =>
      simp only [d315909, d317117, d317997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315910 q = 1) (hb : d317118 q = 1) : d317998 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315910, d317118, d317998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315910, d317118, d317998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315911 q = 1) (hb : d317119 q = 1) : d317999 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315911, d317119, d317999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315911, d317119, d317999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315912 q = 1) (hb : d317120 q = 1) : d318000 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315912, d317120, d318000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315912, d317120, d318000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d315938 q = 1) (hb : d317146 q = 1) : d318026 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315938, d317146, d318026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315938, d317146, d318026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d315939 q = 1) (hb : d317147 q = 1) : d318027 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315939, d317147, d318027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315939, d317147, d318027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83847 (p : Pattern) (ha : d315941 p = 1) (hb : d317149 p = 1) : d318029 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315909 q = 1) (hb : d317117 q = 1) : d317997 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315909, d317117, d317997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83837 q ha hb
    | true =>
      simp only [d315909, d317117, d317997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315910 q = 1) (hb : d317118 q = 1) : d317998 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315910, d317118, d317998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315910, d317118, d317998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315915 q = 1) (hb : d317123 q = 1) : d318003 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315915, d317123, d318003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315915, d317123, d318003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315916 q = 1) (hb : d317124 q = 1) : d318004 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315916, d317124, d318004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315916, d317124, d318004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d315940 q = 1) (hb : d317148 q = 1) : d318028 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315940, d317148, d318028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315940, d317148, d318028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315941 q = 1) (hb : d317149 q = 1) : d318029 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315941, d317149, d318029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315941, d317149, d318029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83848 (p : Pattern) (ha : d315948 p = 1) (hb : d317156 p = 1) : d318036 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315905 q = 1) (hb : d317113 q = 1) : d317993 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315905, d317113, d317993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83836 q ha hb
    | true =>
      simp only [d315905, d317113, d317993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315906 q = 1) (hb : d317114 q = 1) : d317994 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315906, d317114, d317994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315906, d317114, d317994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315909 q = 1) (hb : d317117 q = 1) : d317997 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315909, d317117, d317997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83837 q ha hb
    | true =>
      simp only [d315909, d317117, d317997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315910 q = 1) (hb : d317118 q = 1) : d317998 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315910, d317118, d317998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315910, d317118, d317998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315911 q = 1) (hb : d317119 q = 1) : d317999 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315911, d317119, d317999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315911, d317119, d317999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315946 q = 1) (hb : d317154 q = 1) : d318034 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315946, d317154, d318034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315946, d317154, d318034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d315947 q = 1) (hb : d317155 q = 1) : d318035 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315947, d317155, d318035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315947, d317155, d318035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d315948 q = 1) (hb : d317156 q = 1) : d318036 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315948, d317156, d318036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315948, d317156, d318036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83849 (p : Pattern) (ha : d315951 p = 1) (hb : d317159 p = 1) : d318039 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315909 q = 1) (hb : d317117 q = 1) : d317997 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315909, d317117, d317997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83837 q ha hb
    | true =>
      simp only [d315909, d317117, d317997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315910 q = 1) (hb : d317118 q = 1) : d317998 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315910, d317118, d317998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315910, d317118, d317998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315915 q = 1) (hb : d317123 q = 1) : d318003 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315915, d317123, d318003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315915, d317123, d318003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315949 q = 1) (hb : d317157 q = 1) : d318037 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315949, d317157, d318037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315949, d317157, d318037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315950 q = 1) (hb : d317158 q = 1) : d318038 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315950, d317158, d318038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315950, d317158, d318038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d315951 q = 1) (hb : d317159 q = 1) : d318039 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315951, d317159, d318039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315951, d317159, d318039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83850 (p : Pattern) (ha : d315965 p = 1) (hb : d317171 p = 1) : d318044 p = 1 := by
  have h0 (q : Pattern) (ha : d315963 q = 1) (hb : d317169 q = 1) : d317169 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d315869 q = 1) (hb : d317076 q = 1) : d317076 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d315887 q = 1) (hb : d317091 q = 1) : d317983 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315887, d317091, d317983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315887, d317091, d317983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83834 q ha hb
  have h4 (q : Pattern) (ha : d315888 q = 1) (hb : d317092 q = 1) : d317984 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315888, d317092, d317984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d315888, d317092, d317984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315889 q = 1) (hb : d317093 q = 1) : d317985 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315889, d317093, d317985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d315889, d317093, d317985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315897 q = 1) (hb : d317100 q = 1) : d317100 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d315898 q = 1) (hb : d317101 q = 1) : d317986 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315898, d317101, d317986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83834 q ha hb
    | true =>
      simp only [d315898, d317101, d317986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d315899 q = 1) (hb : d317102 q = 1) : d317987 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315899, d317102, d317987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d315899, d317102, d317987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d315900 q = 1) (hb : d317103 q = 1) : d317988 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315900, d317103, d317988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d315900, d317103, d317988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d315901 q = 1) (hb : d317104 q = 1) : d317989 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d315901, d317104, d317989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315901, d317104, d317989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d315964 q = 1) (hb : d317170 q = 1) : d318043 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d315964, d317170, d318043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d315964, d317170, d318043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d315965 q = 1) (hb : d317171 q = 1) : d318044 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d315965, d317171, d318044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d315965, d317171, d318044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h12 p ha hb
theorem andIntro83851 (p : Pattern) (ha : d315971 p = 1) (hb : d317182 p = 1) : d318050 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315966 q = 1) (hb : d317172 q = 1) : d318045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315966, d317172, d318045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83850 q ha hb
    | true =>
      simp only [d315966, d317172, d318045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315967 q = 1) (hb : d317173 q = 1) : d318046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315967, d317173, d318046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315967, d317173, d318046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315905 q = 1) (hb : d317177 q = 1) : d317993 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315905, d317177, d317993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83844 q ha hb
    | true =>
      simp only [d315905, d317177, d317993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315906 q = 1) (hb : d317178 q = 1) : d317994 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315906, d317178, d317994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315906, d317178, d317994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315968 q = 1) (hb : d317179 q = 1) : d318047 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315968, d317179, d318047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315968, d317179, d318047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315969 q = 1) (hb : d317180 q = 1) : d318048 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315969, d317180, d318048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315969, d317180, d318048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d315970 q = 1) (hb : d317181 q = 1) : d318049 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315970, d317181, d318049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315970, d317181, d318049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d315971 q = 1) (hb : d317182 q = 1) : d318050 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315971, d317182, d318050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315971, d317182, d318050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83852 (p : Pattern) (ha : d315983 p = 1) (hb : d317090 p = 1) : d317982 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315875 q = 1) (hb : d317080 q = 1) : d317977 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315875, d317080, d317977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83832 q ha hb
    | true =>
      simp only [d315875, d317080, d317977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315876 q = 1) (hb : d317081 q = 1) : d317978 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315876, d317081, d317978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d315876, d317081, d317978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d315877 q = 1) (hb : d317082 q = 1) : d317979 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d315877, d317082, d317979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315877, d317082, d317979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315878 q = 1) (hb : d317083 q = 1) : d317980 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d315878, d317083, d317980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315878, d317083, d317980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d315880 q = 1) (hb : d317085 q = 1) : d317095 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315880, d317085, d317095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83833 q ha hb
    | true =>
      simp only [d315880, d317085, d317095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d315881 q = 1) (hb : d317086 q = 1) : d317096 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315881, d317086, d317096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315881, d317086, d317096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d315882 q = 1) (hb : d317087 q = 1) : d317097 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d315882, d317087, d317097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315882, d317087, d317097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d315883 q = 1) (hb : d317088 q = 1) : d317098 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d315883, d317088, d317098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d315883, d317088, d317098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d315884 q = 1) (hb : d317089 q = 1) : d317981 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d315884, d317089, d317981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315884, d317089, d317981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d315982 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d315983 q = 1) (hb : d317090 q = 1) : d317982 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d315983, d317090, d317982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d315983, d317090, d317982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro83853 (p : Pattern) (ha : d315984 p = 1) (hb : d317084 p = 1) : d317094 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d315849 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53306 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2029 q = 1) (hb : d53306 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83831 q ha hb
    | true =>
      simp only [d2029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2030 q = 1) (hb : d315870 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2030, d315870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2030, d315870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2031 q = 1) (hb : d315871 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2031, d315871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2031, d315871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d27032 q = 1) : d27032 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d315872 q = 1) (hb : d317077 q = 1) : d235783 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d315872, d317077, d235783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d315872, d317077, d235783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d315873 q = 1) (hb : d317078 q = 1) : d235784 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d315873, d317078, d235784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d315873, d317078, d235784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d315976 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d315984 q = 1) (hb : d317084 q = 1) : d317094 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d315984, d317084, d317094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d315984, d317084, d317094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro83854 (p : Pattern) (ha : d315990 p = 1) (hb : d317106 p = 1) : d317100 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315985 q = 1) (hb : d317085 q = 1) : d317095 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315985, d317085, d317095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83853 q ha hb
    | true =>
      simp only [d315985, d317085, d317095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315986 q = 1) (hb : d317086 q = 1) : d317096 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315986, d317086, d317096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d315986, d317086, d317096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d315987 q = 1) (hb : d317087 q = 1) : d317097 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d315987, d317087, d317097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315987, d317087, d317097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315988 q = 1) (hb : d317088 q = 1) : d317098 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d315988, d317088, d317098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315988, d317088, d317098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d315989 q = 1) (hb : d317105 q = 1) : d317099 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d315989, d317105, d317099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315989, d317105, d317099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d315990 q = 1) (hb : d317106 q = 1) : d317100 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d315990, d317106, d317100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315990, d317106, d317100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83855 (p : Pattern) (ha : d315996 p = 1) (hb : d317112 p = 1) : d317992 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315869 q = 1) (hb : d317076 q = 1) : d317076 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d315887 q = 1) (hb : d317091 q = 1) : d317983 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315887, d317091, d317983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d315887, d317091, d317983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83834 q ha hb
  have h3 (q : Pattern) (ha : d315888 q = 1) (hb : d317092 q = 1) : d317984 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315888, d317092, d317984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315888, d317092, d317984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315889 q = 1) (hb : d317093 q = 1) : d317985 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315889, d317093, d317985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315889, d317093, d317985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315897 q = 1) (hb : d317100 q = 1) : d317100 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d315898 q = 1) (hb : d317101 q = 1) : d317986 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315898, d317101, d317986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83834 q ha hb
    | true =>
      simp only [d315898, d317101, d317986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d315899 q = 1) (hb : d317102 q = 1) : d317987 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315899, d317102, d317987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315899, d317102, d317987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d315900 q = 1) (hb : d317103 q = 1) : d317988 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315900, d317103, d317988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315900, d317103, d317988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d315901 q = 1) (hb : d317104 q = 1) : d317989 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d315901, d317104, d317989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315901, d317104, d317989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d315991 q = 1) (hb : d317107 q = 1) : d317986 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d315991, d317107, d317986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83852 q ha hb
    | true =>
      simp only [d315991, d317107, d317986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83854 q ha hb
  have h11 (q : Pattern) (ha : d315992 q = 1) (hb : d317108 q = 1) : d317987 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d315992, d317108, d317987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315992, d317108, d317987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d315993 q = 1) (hb : d317109 q = 1) : d317988 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d315993, d317109, d317988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315993, d317109, d317988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d315994 q = 1) (hb : d317110 q = 1) : d317990 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d315994, d317110, d317990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d315994, d317110, d317990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d315995 q = 1) (hb : d317111 q = 1) : d317991 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d315995, d317111, d317991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d315995, d317111, d317991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d315996 q = 1) (hb : d317112 q = 1) : d317992 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d315996, d317112, d317992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d315996, d317112, d317992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h15 p ha hb
theorem andIntro83856 (p : Pattern) (ha : d316002 p = 1) (hb : d317192 p = 1) : d318056 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315997 q = 1) (hb : d317113 q = 1) : d317993 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315997, d317113, d317993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83855 q ha hb
    | true =>
      simp only [d315997, d317113, d317993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315998 q = 1) (hb : d317114 q = 1) : d317994 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315998, d317114, d317994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315998, d317114, d317994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315999 q = 1) (hb : d317189 q = 1) : d318053 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315999, d317189, d318053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315999, d317189, d318053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d316000 q = 1) (hb : d317190 q = 1) : d318054 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d316000, d317190, d318054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d316000, d317190, d318054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d316001 q = 1) (hb : d317191 q = 1) : d318055 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d316001, d317191, d318055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d316001, d317191, d318055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d316002 q = 1) (hb : d317192 q = 1) : d318056 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d316002, d317192, d318056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316002, d317192, d318056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83857 (p : Pattern) (ha : d316008 p = 1) (hb : d317198 p = 1) : d318062 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315942 q = 1) (hb : d317150 q = 1) : d318030 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315942, d317150, d318030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83846 q ha hb
    | true =>
      simp only [d315942, d317150, d318030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83847 q ha hb
  have h2 (q : Pattern) (ha : d315943 q = 1) (hb : d317151 q = 1) : d318031 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315943, d317151, d318031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315943, d317151, d318031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315944 q = 1) (hb : d317152 q = 1) : d318032 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315944, d317152, d318032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315944, d317152, d318032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315945 q = 1) (hb : d317153 q = 1) : d318033 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315945, d317153, d318033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315945, d317153, d318033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315952 q = 1) (hb : d317160 q = 1) : d318040 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315952, d317160, d318040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83848 q ha hb
    | true =>
      simp only [d315952, d317160, d318040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83849 q ha hb
  have h6 (q : Pattern) (ha : d315953 q = 1) (hb : d317161 q = 1) : d318041 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315953, d317161, d318041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315953, d317161, d318041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d315954 q = 1) (hb : d317162 q = 1) : d318042 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315954, d317162, d318042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315954, d317162, d318042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d315972 q = 1) (hb : d317187 q = 1) : d318051 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315972, d317187, d318051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83851 q ha hb
    | true =>
      simp only [d315972, d317187, d318051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83845 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d315919 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d315973 q = 1) (hb : d317188 q = 1) : d318052 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315973, d317188, d318052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d315973, d317188, d318052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d316003 q = 1) (hb : d317193 q = 1) : d318057 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d316003, d317193, d318057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83856 q ha hb
    | true =>
      simp only [d316003, d317193, d318057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d316004 q = 1) (hb : d317194 q = 1) : d318058 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d316004, d317194, d318058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d316004, d317194, d318058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d316005 q = 1) (hb : d317195 q = 1) : d318059 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d316005, d317195, d318059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d316005, d317195, d318059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d316006 q = 1) (hb : d317196 q = 1) : d318060 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d316006, d317196, d318060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d316006, d317196, d318060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d316007 q = 1) (hb : d317197 q = 1) : d318061 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d316007, d317197, d318061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d316007, d317197, d318061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d316008 q = 1) (hb : d317198 q = 1) : d318062 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d316008, d317198, d318062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316008, d317198, d318062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro83858 (p : Pattern) (ha : d315927 p = 1) (hb : d317211 p = 1) : d318015 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315905 q = 1) (hb : d317177 q = 1) : d317993 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315905, d317177, d317993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83844 q ha hb
    | true =>
      simp only [d315905, d317177, d317993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315906 q = 1) (hb : d317178 q = 1) : d317994 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315906, d317178, d317994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315906, d317178, d317994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315909 q = 1) (hb : d317117 q = 1) : d317997 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315909, d317117, d317997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83837 q ha hb
    | true =>
      simp only [d315909, d317117, d317997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315910 q = 1) (hb : d317118 q = 1) : d317998 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315910, d317118, d317998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315910, d317118, d317998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315911 q = 1) (hb : d317183 q = 1) : d317999 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315911, d317183, d317999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315911, d317183, d317999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315912 q = 1) (hb : d317184 q = 1) : d318000 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315912, d317184, d318000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315912, d317184, d318000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d315913 q = 1) (hb : d317185 q = 1) : d318001 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315913, d317185, d318001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315913, d317185, d318001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d315927 q = 1) (hb : d317211 q = 1) : d318015 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d315927, d317211, d318015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d315927, d317211, d318015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro83859 (p : Pattern) (ha : d316009 p = 1) (hb : d317199 p = 1) : d318063 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315905 q = 1) (hb : d317113 q = 1) : d317993 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315905, d317113, d317993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83836 q ha hb
    | true =>
      simp only [d315905, d317113, d317993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315906 q = 1) (hb : d317114 q = 1) : d317994 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315906, d317114, d317994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315906, d317114, d317994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315909 q = 1) (hb : d317117 q = 1) : d317997 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315909, d317117, d317997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83837 q ha hb
    | true =>
      simp only [d315909, d317117, d317997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315910 q = 1) (hb : d317118 q = 1) : d317998 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315910, d317118, d317998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315910, d317118, d317998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315911 q = 1) (hb : d317119 q = 1) : d317999 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315911, d317119, d317999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315911, d317119, d317999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315912 q = 1) (hb : d317120 q = 1) : d318000 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315912, d317120, d318000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315912, d317120, d318000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d315938 q = 1) (hb : d317146 q = 1) : d318026 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315938, d317146, d318026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315938, d317146, d318026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d316009 q = 1) (hb : d317199 q = 1) : d318063 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d316009, d317199, d318063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d316009, d317199, d318063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro83860 (p : Pattern) (ha : d316010 p = 1) (hb : d317200 p = 1) : d318064 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315909 q = 1) (hb : d317117 q = 1) : d317997 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315909, d317117, d317997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83837 q ha hb
    | true =>
      simp only [d315909, d317117, d317997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315910 q = 1) (hb : d317118 q = 1) : d317998 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315910, d317118, d317998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315910, d317118, d317998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315915 q = 1) (hb : d317123 q = 1) : d318003 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315915, d317123, d318003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315915, d317123, d318003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315916 q = 1) (hb : d317124 q = 1) : d318004 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315916, d317124, d318004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315916, d317124, d318004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d315940 q = 1) (hb : d317148 q = 1) : d318028 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315940, d317148, d318028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315940, d317148, d318028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d316010 q = 1) (hb : d317200 q = 1) : d318064 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d316010, d317200, d318064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316010, d317200, d318064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83861 (p : Pattern) (ha : d316015 p = 1) (hb : d317205 p = 1) : d318069 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315905 q = 1) (hb : d317113 q = 1) : d317993 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315905, d317113, d317993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83836 q ha hb
    | true =>
      simp only [d315905, d317113, d317993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315906 q = 1) (hb : d317114 q = 1) : d317994 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315906, d317114, d317994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315906, d317114, d317994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315909 q = 1) (hb : d317117 q = 1) : d317997 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315909, d317117, d317997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83837 q ha hb
    | true =>
      simp only [d315909, d317117, d317997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315910 q = 1) (hb : d317118 q = 1) : d317998 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315910, d317118, d317998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315910, d317118, d317998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315911 q = 1) (hb : d317119 q = 1) : d317999 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315911, d317119, d317999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315911, d317119, d317999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315946 q = 1) (hb : d317154 q = 1) : d318034 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315946, d317154, d318034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315946, d317154, d318034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d315947 q = 1) (hb : d317155 q = 1) : d318035 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315947, d317155, d318035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315947, d317155, d318035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d316015 q = 1) (hb : d317205 q = 1) : d318069 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d316015, d317205, d318069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d316015, d317205, d318069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro83862 (p : Pattern) (ha : d316016 p = 1) (hb : d317206 p = 1) : d318070 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315909 q = 1) (hb : d317117 q = 1) : d317997 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315909, d317117, d317997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83837 q ha hb
    | true =>
      simp only [d315909, d317117, d317997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315910 q = 1) (hb : d317118 q = 1) : d317998 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315910, d317118, d317998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315910, d317118, d317998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315915 q = 1) (hb : d317123 q = 1) : d318003 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315915, d317123, d318003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315915, d317123, d318003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315949 q = 1) (hb : d317157 q = 1) : d318037 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315949, d317157, d318037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315949, d317157, d318037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315950 q = 1) (hb : d317158 q = 1) : d318038 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315950, d317158, d318038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315950, d317158, d318038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d316016 q = 1) (hb : d317206 q = 1) : d318070 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d316016, d317206, d318070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316016, d317206, d318070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83863 (p : Pattern) (ha : d316020 p = 1) (hb : d317210 p = 1) : d318074 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315966 q = 1) (hb : d317172 q = 1) : d318045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315966, d317172, d318045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83850 q ha hb
    | true =>
      simp only [d315966, d317172, d318045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315967 q = 1) (hb : d317173 q = 1) : d318046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315967, d317173, d318046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315967, d317173, d318046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315905 q = 1) (hb : d317177 q = 1) : d317993 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315905, d317177, d317993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83844 q ha hb
    | true =>
      simp only [d315905, d317177, d317993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315906 q = 1) (hb : d317178 q = 1) : d317994 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315906, d317178, d317994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315906, d317178, d317994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315968 q = 1) (hb : d317179 q = 1) : d318047 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315968, d317179, d318047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315968, d317179, d318047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315969 q = 1) (hb : d317180 q = 1) : d318048 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d315969, d317180, d318048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315969, d317180, d318048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d315970 q = 1) (hb : d317181 q = 1) : d318049 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d315970, d317181, d318049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315970, d317181, d318049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d316020 q = 1) (hb : d317210 q = 1) : d318074 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d316020, d317210, d318074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d316020, d317210, d318074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro83864 (p : Pattern) (ha : d316023 p = 1) (hb : d317214 p = 1) : d318077 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315997 q = 1) (hb : d317113 q = 1) : d317993 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d315997, d317113, d317993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83855 q ha hb
    | true =>
      simp only [d315997, d317113, d317993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d315998 q = 1) (hb : d317114 q = 1) : d317994 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d315998, d317114, d317994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315998, d317114, d317994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315999 q = 1) (hb : d317189 q = 1) : d318053 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d315999, d317189, d318053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315999, d317189, d318053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d316000 q = 1) (hb : d317190 q = 1) : d318054 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d316000, d317190, d318054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d316000, d317190, d318054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d316001 q = 1) (hb : d317191 q = 1) : d318055 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d316001, d317191, d318055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d316001, d317191, d318055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d316023 q = 1) (hb : d317214 q = 1) : d318077 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d316023, d317214, d318077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316023, d317214, d318077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83865 (p : Pattern) (ha : d316029 p = 1) (hb : d317220 p = 1) : d318083 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315942 q = 1) (hb : d317150 q = 1) : d318030 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315942, d317150, d318030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83846 q ha hb
    | true =>
      simp only [d315942, d317150, d318030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83847 q ha hb
  have h2 (q : Pattern) (ha : d315943 q = 1) (hb : d317151 q = 1) : d318031 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315943, d317151, d318031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315943, d317151, d318031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315944 q = 1) (hb : d317152 q = 1) : d318032 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315944, d317152, d318032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315944, d317152, d318032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315945 q = 1) (hb : d317153 q = 1) : d318033 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315945, d317153, d318033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315945, d317153, d318033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315952 q = 1) (hb : d317160 q = 1) : d318040 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315952, d317160, d318040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83848 q ha hb
    | true =>
      simp only [d315952, d317160, d318040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83849 q ha hb
  have h6 (q : Pattern) (ha : d315953 q = 1) (hb : d317161 q = 1) : d318041 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315953, d317161, d318041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315953, d317161, d318041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d315954 q = 1) (hb : d317162 q = 1) : d318042 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315954, d317162, d318042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315954, d317162, d318042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d315972 q = 1) (hb : d317187 q = 1) : d318051 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315972, d317187, d318051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83851 q ha hb
    | true =>
      simp only [d315972, d317187, d318051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83845 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d315919 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d315973 q = 1) (hb : d317188 q = 1) : d318052 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315973, d317188, d318052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d315973, d317188, d318052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d316003 q = 1) (hb : d317193 q = 1) : d318057 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d316003, d317193, d318057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83856 q ha hb
    | true =>
      simp only [d316003, d317193, d318057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d316004 q = 1) (hb : d317194 q = 1) : d318058 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d316004, d317194, d318058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d316004, d317194, d318058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d316005 q = 1) (hb : d317195 q = 1) : d318059 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d316005, d317195, d318059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d316005, d317195, d318059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d316006 q = 1) (hb : d317196 q = 1) : d318060 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d316006, d317196, d318060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d316006, d317196, d318060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d316007 q = 1) (hb : d317197 q = 1) : d318061 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d316007, d317197, d318061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d316007, d317197, d318061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d316011 q = 1) (hb : d317201 q = 1) : d318065 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d316011, d317201, d318065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83859 q ha hb
    | true =>
      simp only [d316011, d317201, d318065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83860 q ha hb
  have h17 (q : Pattern) (ha : d316012 q = 1) (hb : d317202 q = 1) : d318066 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d316012, d317202, d318066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316012, d317202, d318066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d316013 q = 1) (hb : d317203 q = 1) : d318067 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d316013, d317203, d318067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d316013, d317203, d318067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d316014 q = 1) (hb : d317204 q = 1) : d318068 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d316014, d317204, d318068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316014, d317204, d318068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d316017 q = 1) (hb : d317207 q = 1) : d318071 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d316017, d317207, d318071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83861 q ha hb
    | true =>
      simp only [d316017, d317207, d318071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83862 q ha hb
  have h21 (q : Pattern) (ha : d316018 q = 1) (hb : d317208 q = 1) : d318072 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d316018, d317208, d318072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316018, d317208, d318072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d316019 q = 1) (hb : d317209 q = 1) : d318073 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d316019, d317209, d318073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d316019, d317209, d318073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d316021 q = 1) (hb : d317212 q = 1) : d318075 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d316021, d317212, d318075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83863 q ha hb
    | true =>
      simp only [d316021, d317212, d318075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83858 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d315929 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d316022 q = 1) (hb : d317213 q = 1) : d318076 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d316022, d317213, d318076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d316022, d317213, d318076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d316024 q = 1) (hb : d317215 q = 1) : d318078 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d316024, d317215, d318078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83864 q ha hb
    | true =>
      simp only [d316024, d317215, d318078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d316025 q = 1) (hb : d317216 q = 1) : d318079 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d316025, d317216, d318079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d316025, d317216, d318079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d316026 q = 1) (hb : d317217 q = 1) : d318080 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d316026, d317217, d318080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d316026, d317217, d318080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d316027 q = 1) (hb : d317218 q = 1) : d318081 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d316027, d317218, d318081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d316027, d317218, d318081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d316028 q = 1) (hb : d317219 q = 1) : d318082 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d316028, d317219, d318082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d316028, d317219, d318082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d316029 q = 1) (hb : d317220 q = 1) : d318083 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d316029, d317220, d318083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d316029, d317220, d318083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro83866 (p : Pattern) (ha : d316036 p = 1) (hb : d317232 p = 1) : d318090 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315919 q = 1) (hb : d317222 q = 1) : d318007 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315919, d317222, d318007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83845 q ha hb
    | true =>
      simp only [d315919, d317222, d318007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83839 q ha hb
  have h2 (q : Pattern) (ha : d315920 q = 1) (hb : d317223 q = 1) : d318008 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315920, d317223, d318008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315920, d317223, d318008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315921 q = 1) (hb : d317224 q = 1) : d318009 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315921, d317224, d318009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315921, d317224, d318009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d315922 q = 1) (hb : d317225 q = 1) : d318010 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315922, d317225, d318010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315922, d317225, d318010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315923 q = 1) (hb : d317226 q = 1) : d318011 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d315923, d317226, d318011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315923, d317226, d318011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d316031 q = 1) (hb : d317227 q = 1) : d318085 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d316031, d317227, d318085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83839 q ha hb
    | true =>
      simp only [d316031, d317227, d318085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d316032 q = 1) (hb : d317228 q = 1) : d318086 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d316032, d317228, d318086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316032, d317228, d318086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d316033 q = 1) (hb : d317229 q = 1) : d318087 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d316033, d317229, d318087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d316033, d317229, d318087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d316034 q = 1) (hb : d317230 q = 1) : d318088 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d316034, d317230, d318088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316034, d317230, d318088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d316035 q = 1) (hb : d317231 q = 1) : d318089 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d316035, d317231, d318089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316035, d317231, d318089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d316036 q = 1) (hb : d317232 q = 1) : d318090 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d316036, d317232, d318090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316036, d317232, d318090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro83867 (p : Pattern) (ha : d316042 p = 1) (hb : d317238 p = 1) : d318096 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316031 q = 1) (hb : d317227 q = 1) : d318085 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d316031, d317227, d318085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83839 q ha hb
    | true =>
      simp only [d316031, d317227, d318085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d316032 q = 1) (hb : d317228 q = 1) : d318086 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d316032, d317228, d318086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316032, d317228, d318086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d316033 q = 1) (hb : d317229 q = 1) : d318087 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d316033, d317229, d318087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d316033, d317229, d318087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d316034 q = 1) (hb : d317230 q = 1) : d318088 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d316034, d317230, d318088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316034, d317230, d318088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d316035 q = 1) (hb : d317231 q = 1) : d318089 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d316035, d317231, d318089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316035, d317231, d318089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d316037 q = 1) (hb : d317233 q = 1) : d318091 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d316037, d317233, d318091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83842 q ha hb
    | true =>
      simp only [d316037, d317233, d318091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d316038 q = 1) (hb : d317234 q = 1) : d318092 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d316038, d317234, d318092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316038, d317234, d318092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d316039 q = 1) (hb : d317235 q = 1) : d318093 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d316039, d317235, d318093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d316039, d317235, d318093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d316040 q = 1) (hb : d317236 q = 1) : d318094 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d316040, d317236, d318094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316040, d317236, d318094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d316041 q = 1) (hb : d317237 q = 1) : d318095 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d316041, d317237, d318095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316041, d317237, d318095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d316042 q = 1) (hb : d317238 q = 1) : d318096 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d316042, d317238, d318096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316042, d317238, d318096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro83868 (p : Pattern) (ha : d316049 p = 1) (hb : d317245 p = 1) : d318103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316021 q = 1) (hb : d317212 q = 1) : d318075 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d316021, d317212, d318075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83863 q ha hb
    | true =>
      simp only [d316021, d317212, d318075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83858 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d315929 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d316022 q = 1) (hb : d317213 q = 1) : d318076 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d316022, d317213, d318076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d316022, d317213, d318076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d316024 q = 1) (hb : d317215 q = 1) : d318078 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d316024, d317215, d318078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83864 q ha hb
    | true =>
      simp only [d316024, d317215, d318078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d316025 q = 1) (hb : d317216 q = 1) : d318079 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d316025, d317216, d318079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d316025, d317216, d318079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d316026 q = 1) (hb : d317217 q = 1) : d318080 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d316026, d317217, d318080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d316026, d317217, d318080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d316047 q = 1) (hb : d317243 q = 1) : d318101 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d316047, d317243, d318101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316047, d317243, d318101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d316048 q = 1) (hb : d317244 q = 1) : d318102 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d316048, d317244, d318102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316048, d317244, d318102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d316049 q = 1) (hb : d317245 q = 1) : d318103 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d316049, d317245, d318103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316049, d317245, d318103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro83869 (p : Pattern) (ha : d316051 p = 1) (hb : d317247 p = 1) : d318105 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316037 q = 1) (hb : d317233 q = 1) : d318091 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d316037, d317233, d318091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83842 q ha hb
    | true =>
      simp only [d316037, d317233, d318091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d316038 q = 1) (hb : d317234 q = 1) : d318092 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d316038, d317234, d318092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316038, d317234, d318092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d316039 q = 1) (hb : d317235 q = 1) : d318093 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d316039, d317235, d318093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d316039, d317235, d318093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d316040 q = 1) (hb : d317236 q = 1) : d318094 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d316040, d317236, d318094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316040, d317236, d318094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d316041 q = 1) (hb : d317237 q = 1) : d318095 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d316041, d317237, d318095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316041, d317237, d318095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d316051 q = 1) (hb : d317247 q = 1) : d318105 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d316051, d317247, d318105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316051, d317247, d318105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83870 (p : Pattern) (ha : d316087 p = 1) (hb : d317279 p = 1) : d318116 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316078 q = 1) (hb : d317270 q = 1) : d318111 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d316078, d317270, d318111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316078, d317270, d318111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83832 q ha hb
  have h2 (q : Pattern) (ha : d315875 q = 1) (hb : d317080 q = 1) : d317977 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315875, d317080, d317977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83832 q ha hb
    | true =>
      simp only [d315875, d317080, d317977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d316079 q = 1) (hb : d317271 q = 1) : d318112 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d316079, d317271, d318112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d316079, d317271, d318112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315876 q = 1) (hb : d317081 q = 1) : d317978 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315876, d317081, d317978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315876, d317081, d317978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d316080 q = 1) (hb : d317272 q = 1) : d318113 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d316080, d317272, d318113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d316080, d317272, d318113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d316081 q = 1) (hb : d317273 q = 1) : d318114 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d316081, d317273, d318114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316081, d317273, d318114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d316082 q = 1) (hb : d317274 q = 1) : d317283 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d316082, d317274, d317283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316082, d317274, d317283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83833 q ha hb
  have h8 (q : Pattern) (ha : d315880 q = 1) (hb : d317085 q = 1) : d317095 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315880, d317085, d317095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83833 q ha hb
    | true =>
      simp only [d315880, d317085, d317095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d316083 q = 1) (hb : d317275 q = 1) : d317284 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d316083, d317275, d317284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d316083, d317275, d317284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d315881 q = 1) (hb : d317086 q = 1) : d317096 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315881, d317086, d317096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d315881, d317086, d317096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d316084 q = 1) (hb : d317276 q = 1) : d317285 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d316084, d317276, d317285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d316084, d317276, d317285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d316085 q = 1) (hb : d317277 q = 1) : d317286 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d316085, d317277, d317286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d316085, d317277, d317286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d316086 q = 1) (hb : d317278 q = 1) : d318115 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d316086, d317278, d318115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d316086, d317278, d318115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d316072 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d316087 q = 1) (hb : d317279 q = 1) : d318116 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d316087, d317279, d318116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d316087, d317279, d318116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro83871 (p : Pattern) (ha : d316103 p = 1) (hb : d317294 p = 1) : d318125 p = 1 := by
  have h0 (q : Pattern) (ha : d316077 q = 1) (hb : d317269 q = 1) : d317269 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d316068 q = 1) (hb : d317262 q = 1) : d317262 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d316088 q = 1) (hb : d317280 q = 1) : d318117 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d316088, d317280, d318117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d316088, d317280, d318117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83870 q ha hb
  have h4 (q : Pattern) (ha : d316089 q = 1) (hb : d317281 q = 1) : d318118 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d316089, d317281, d318118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d316089, d317281, d318118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d316090 q = 1) (hb : d317282 q = 1) : d318119 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d316090, d317282, d318119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d316090, d317282, d318119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d316097 q = 1) (hb : d317288 q = 1) : d317288 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d316098 q = 1) (hb : d317289 q = 1) : d318120 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d316098, d317289, d318120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83870 q ha hb
    | true =>
      simp only [d316098, d317289, d318120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d316099 q = 1) (hb : d317290 q = 1) : d318121 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d316099, d317290, d318121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d316099, d317290, d318121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d316100 q = 1) (hb : d317291 q = 1) : d318122 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d316100, d317291, d318122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d316100, d317291, d318122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d316101 q = 1) (hb : d317292 q = 1) : d318123 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d316101, d317292, d318123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316101, d317292, d318123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d316102 q = 1) (hb : d317293 q = 1) : d318124 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d316102, d317293, d318124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d316102, d317293, d318124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d316103 q = 1) (hb : d317294 q = 1) : d318125 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d316103, d317294, d318125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d316103, d317294, d318125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h12 p ha hb
theorem andIntro83872 (p : Pattern) (ha : d316108 p = 1) (hb : d317299 p = 1) : d318130 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316068 q = 1) (hb : d317262 q = 1) : d317262 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d316088 q = 1) (hb : d317280 q = 1) : d318117 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d316088, d317280, d318117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d316088, d317280, d318117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83870 q ha hb
  have h3 (q : Pattern) (ha : d316089 q = 1) (hb : d317281 q = 1) : d318118 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d316089, d317281, d318118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316089, d317281, d318118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d316090 q = 1) (hb : d317282 q = 1) : d318119 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d316090, d317282, d318119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316090, d317282, d318119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d316097 q = 1) (hb : d317288 q = 1) : d317288 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d316098 q = 1) (hb : d317289 q = 1) : d318120 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d316098, d317289, d318120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83870 q ha hb
    | true =>
      simp only [d316098, d317289, d318120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d316099 q = 1) (hb : d317290 q = 1) : d318121 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d316099, d317290, d318121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316099, d317290, d318121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d316100 q = 1) (hb : d317291 q = 1) : d318122 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d316100, d317291, d318122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316100, d317291, d318122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d316101 q = 1) (hb : d317292 q = 1) : d318123 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d316101, d317292, d318123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d316101, d317292, d318123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d316106 q = 1) (hb : d317297 q = 1) : d318128 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d316106, d317297, d318128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d316106, d317297, d318128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d316107 q = 1) (hb : d317298 q = 1) : d318129 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d316107, d317298, d318129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d316107, d317298, d318129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d316108 q = 1) (hb : d317299 q = 1) : d318130 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d316108, d317299, d318130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d316108, d317299, d318130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro83873 (p : Pattern) (ha : d316114 p = 1) (hb : d317305 p = 1) : d318136 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316104 q = 1) (hb : d317295 q = 1) : d318126 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d316104, d317295, d318126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83871 q ha hb
    | true =>
      simp only [d316104, d317295, d318126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d316105 q = 1) (hb : d317296 q = 1) : d318127 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d316105, d317296, d318127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316105, d317296, d318127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d316109 q = 1) (hb : d317300 q = 1) : d318131 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d316109, d317300, d318131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83872 q ha hb
    | true =>
      simp only [d316109, d317300, d318131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d316110 q = 1) (hb : d317301 q = 1) : d318132 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d316110, d317301, d318132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316110, d317301, d318132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d316111 q = 1) (hb : d317302 q = 1) : d318133 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d316111, d317302, d318133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d316111, d317302, d318133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d316112 q = 1) (hb : d317303 q = 1) : d318134 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d316112, d317303, d318134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316112, d317303, d318134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d316113 q = 1) (hb : d317304 q = 1) : d318135 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d316113, d317304, d318135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d316113, d317304, d318135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d316114 q = 1) (hb : d317305 q = 1) : d318136 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d316114, d317305, d318136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d316114, d317305, d318136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro83874 (p : Pattern) (ha : d316097 p = 1) (hb : d317307 p = 1) : d317288 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316082 q = 1) (hb : d317274 q = 1) : d317283 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d316082, d317274, d317283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316082, d317274, d317283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83833 q ha hb
  have h2 (q : Pattern) (ha : d315880 q = 1) (hb : d317085 q = 1) : d317095 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315880, d317085, d317095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83833 q ha hb
    | true =>
      simp only [d315880, d317085, d317095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d316083 q = 1) (hb : d317275 q = 1) : d317284 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d316083, d317275, d317284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d316083, d317275, d317284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315881 q = 1) (hb : d317086 q = 1) : d317096 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315881, d317086, d317096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315881, d317086, d317096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d316084 q = 1) (hb : d317276 q = 1) : d317285 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d316084, d317276, d317285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d316084, d317276, d317285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d316085 q = 1) (hb : d317277 q = 1) : d317286 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d316085, d317277, d317286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316085, d317277, d317286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d316091 q = 1) (hb : d317306 q = 1) : d317287 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d316091, d317306, d317287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d316091, d317306, d317287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d316096 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d316097 q = 1) (hb : d317307 q = 1) : d317288 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d316097, d317307, d317288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d316097, d317307, d317288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro83875 (p : Pattern) (ha : d316116 p = 1) (hb : d317313 p = 1) : d318138 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316098 q = 1) (hb : d317308 q = 1) : d318120 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d316098, d317308, d318120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83870 q ha hb
    | true =>
      simp only [d316098, d317308, d318120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83874 q ha hb
  have h2 (q : Pattern) (ha : d316099 q = 1) (hb : d317309 q = 1) : d318121 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d316099, d317309, d318121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316099, d317309, d318121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d316100 q = 1) (hb : d317310 q = 1) : d318122 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d316100, d317310, d318122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316100, d317310, d318122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d316106 q = 1) (hb : d317311 q = 1) : d318128 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d316106, d317311, d318128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d316106, d317311, d318128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d316115 q = 1) (hb : d317312 q = 1) : d318137 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d316115, d317312, d318137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d316115, d317312, d318137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d316116 q = 1) (hb : d317313 q = 1) : d318138 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d316116, d317313, d318138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316116, d317313, d318138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83876 (p : Pattern) (ha : d316122 p = 1) (hb : d317319 p = 1) : d318144 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316109 q = 1) (hb : d317300 q = 1) : d318131 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d316109, d317300, d318131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83872 q ha hb
    | true =>
      simp only [d316109, d317300, d318131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d316110 q = 1) (hb : d317301 q = 1) : d318132 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d316110, d317301, d318132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316110, d317301, d318132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d316117 q = 1) (hb : d317314 q = 1) : d318139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d316117, d317314, d318139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83875 q ha hb
    | true =>
      simp only [d316117, d317314, d318139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d316118 q = 1) (hb : d317315 q = 1) : d318140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d316118, d317315, d318140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316118, d317315, d318140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d316119 q = 1) (hb : d317316 q = 1) : d318141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d316119, d317316, d318141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d316119, d317316, d318141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d316120 q = 1) (hb : d317317 q = 1) : d318142 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d316120, d317317, d318142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316120, d317317, d318142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d316121 q = 1) (hb : d317318 q = 1) : d318143 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d316121, d317318, d318143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d316121, d317318, d318143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d316122 q = 1) (hb : d317319 q = 1) : d318144 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d316122, d317319, d318144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d316122, d317319, d318144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro83877 (p : Pattern) (ha : d316135 p = 1) (hb : d317279 p = 1) : d318116 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316078 q = 1) (hb : d317270 q = 1) : d318111 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d316078, d317270, d318111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316078, d317270, d318111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83832 q ha hb
  have h2 (q : Pattern) (ha : d315875 q = 1) (hb : d317080 q = 1) : d317977 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315875, d317080, d317977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83832 q ha hb
    | true =>
      simp only [d315875, d317080, d317977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d316079 q = 1) (hb : d317271 q = 1) : d318112 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d316079, d317271, d318112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d316079, d317271, d318112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315876 q = 1) (hb : d317081 q = 1) : d317978 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315876, d317081, d317978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315876, d317081, d317978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d316080 q = 1) (hb : d317272 q = 1) : d318113 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d316080, d317272, d318113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d316080, d317272, d318113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d316081 q = 1) (hb : d317273 q = 1) : d318114 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d316081, d317273, d318114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316081, d317273, d318114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d316082 q = 1) (hb : d317274 q = 1) : d317283 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d316082, d317274, d317283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316082, d317274, d317283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83833 q ha hb
  have h8 (q : Pattern) (ha : d315880 q = 1) (hb : d317085 q = 1) : d317095 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315880, d317085, d317095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83833 q ha hb
    | true =>
      simp only [d315880, d317085, d317095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d316083 q = 1) (hb : d317275 q = 1) : d317284 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d316083, d317275, d317284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d316083, d317275, d317284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d315881 q = 1) (hb : d317086 q = 1) : d317096 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315881, d317086, d317096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d315881, d317086, d317096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d316084 q = 1) (hb : d317276 q = 1) : d317285 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d316084, d317276, d317285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d316084, d317276, d317285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d316085 q = 1) (hb : d317277 q = 1) : d317286 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d316085, d317277, d317286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d316085, d317277, d317286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d316086 q = 1) (hb : d317278 q = 1) : d318115 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d316086, d317278, d318115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d316086, d317278, d318115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d316134 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d316135 q = 1) (hb : d317279 q = 1) : d318116 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d316135, d317279, d318116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d316135, d317279, d318116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro83878 (p : Pattern) (ha : d316141 p = 1) (hb : d317307 p = 1) : d317288 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316136 q = 1) (hb : d317274 q = 1) : d317283 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d316136, d317274, d317283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316136, d317274, d317283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83853 q ha hb
  have h2 (q : Pattern) (ha : d315985 q = 1) (hb : d317085 q = 1) : d317095 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315985, d317085, d317095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83853 q ha hb
    | true =>
      simp only [d315985, d317085, d317095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d316137 q = 1) (hb : d317275 q = 1) : d317284 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d316137, d317275, d317284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d316137, d317275, d317284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315986 q = 1) (hb : d317086 q = 1) : d317096 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315986, d317086, d317096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315986, d317086, d317096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d316138 q = 1) (hb : d317276 q = 1) : d317285 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d316138, d317276, d317285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d316138, d317276, d317285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d316139 q = 1) (hb : d317277 q = 1) : d317286 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d316139, d317277, d317286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316139, d317277, d317286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d316140 q = 1) (hb : d317306 q = 1) : d317287 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d316140, d317306, d317287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d316140, d317306, d317287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d316141 q = 1) (hb : d317307 q = 1) : d317288 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d316141, d317307, d317288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d316141, d317307, d317288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro83879 (p : Pattern) (ha : d316147 p = 1) (hb : d317323 p = 1) : d318130 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316068 q = 1) (hb : d317262 q = 1) : d317262 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d316088 q = 1) (hb : d317280 q = 1) : d318117 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d316088, d317280, d318117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d316088, d317280, d318117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83870 q ha hb
  have h3 (q : Pattern) (ha : d316089 q = 1) (hb : d317281 q = 1) : d318118 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d316089, d317281, d318118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316089, d317281, d318118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d316090 q = 1) (hb : d317282 q = 1) : d318119 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d316090, d317282, d318119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316090, d317282, d318119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d316097 q = 1) (hb : d317288 q = 1) : d317288 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d316098 q = 1) (hb : d317289 q = 1) : d318120 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d316098, d317289, d318120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83870 q ha hb
    | true =>
      simp only [d316098, d317289, d318120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d316099 q = 1) (hb : d317290 q = 1) : d318121 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d316099, d317290, d318121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316099, d317290, d318121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d316100 q = 1) (hb : d317291 q = 1) : d318122 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d316100, d317291, d318122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316100, d317291, d318122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d316101 q = 1) (hb : d317292 q = 1) : d318123 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d316101, d317292, d318123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d316101, d317292, d318123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d316142 q = 1) (hb : d317308 q = 1) : d318120 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d316142, d317308, d318120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83877 q ha hb
    | true =>
      simp only [d316142, d317308, d318120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83878 q ha hb
  have h11 (q : Pattern) (ha : d316143 q = 1) (hb : d317309 q = 1) : d318121 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d316143, d317309, d318121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316143, d317309, d318121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d316144 q = 1) (hb : d317310 q = 1) : d318122 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d316144, d317310, d318122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316144, d317310, d318122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d316145 q = 1) (hb : d317311 q = 1) : d318128 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d316145, d317311, d318128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d316145, d317311, d318128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d316146 q = 1) (hb : d317322 q = 1) : d318129 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d316146, d317322, d318129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d316146, d317322, d318129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d316147 q = 1) (hb : d317323 q = 1) : d318130 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d316147, d317323, d318130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d316147, d317323, d318130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h15 p ha hb
theorem andIntro83880 (p : Pattern) (ha : d316153 p = 1) (hb : d317329 p = 1) : d318150 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316148 q = 1) (hb : d317324 q = 1) : d318131 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d316148, d317324, d318131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83879 q ha hb
    | true =>
      simp only [d316148, d317324, d318131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d316149 q = 1) (hb : d317325 q = 1) : d318132 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d316149, d317325, d318132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316149, d317325, d318132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d316150 q = 1) (hb : d317326 q = 1) : d318147 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d316150, d317326, d318147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d316150, d317326, d318147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d316151 q = 1) (hb : d317327 q = 1) : d318148 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d316151, d317327, d318148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d316151, d317327, d318148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d316152 q = 1) (hb : d317328 q = 1) : d318149 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d316152, d317328, d318149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d316152, d317328, d318149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d316153 q = 1) (hb : d317329 q = 1) : d318150 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d316153, d317329, d318150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316153, d317329, d318150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83881 (p : Pattern) (ha : d316159 p = 1) (hb : d317335 p = 1) : d318156 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316123 q = 1) (hb : d317320 q = 1) : d318145 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d316123, d317320, d318145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83873 q ha hb
    | true =>
      simp only [d316123, d317320, d318145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83876 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d316128 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d316129 q = 1) (hb : d317321 q = 1) : d318146 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d316129, d317321, d318146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d316129, d317321, d318146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d316154 q = 1) (hb : d317330 q = 1) : d318151 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d316154, d317330, d318151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83880 q ha hb
    | true =>
      simp only [d316154, d317330, d318151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d316155 q = 1) (hb : d317331 q = 1) : d318152 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d316155, d317331, d318152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d316155, d317331, d318152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d316156 q = 1) (hb : d317332 q = 1) : d318153 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d316156, d317332, d318153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d316156, d317332, d318153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d316157 q = 1) (hb : d317333 q = 1) : d318154 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d316157, d317333, d318154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316157, d317333, d318154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d316158 q = 1) (hb : d317334 q = 1) : d318155 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d316158, d317334, d318155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316158, d317334, d318155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d316159 q = 1) (hb : d317335 q = 1) : d318156 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d316159, d317335, d318156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316159, d317335, d318156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro83882 (p : Pattern) (ha : d316127 p = 1) (hb : d317340 p = 1) : d318161 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316117 q = 1) (hb : d317314 q = 1) : d318139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d316117, d317314, d318139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83875 q ha hb
    | true =>
      simp only [d316117, d317314, d318139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d316118 q = 1) (hb : d317315 q = 1) : d318140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d316118, d317315, d318140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316118, d317315, d318140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d316124 q = 1) (hb : d317337 q = 1) : d318158 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d316124, d317337, d318158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d316124, d317337, d318158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d316125 q = 1) (hb : d317338 q = 1) : d318159 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d316125, d317338, d318159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d316125, d317338, d318159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d316126 q = 1) (hb : d317339 q = 1) : d318160 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d316126, d317339, d318160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d316126, d317339, d318160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d316127 q = 1) (hb : d317340 q = 1) : d318161 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d316127, d317340, d318161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316127, d317340, d318161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83883 (p : Pattern) (ha : d316166 p = 1) (hb : d317346 p = 1) : d318167 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316161 q = 1) (hb : d317341 q = 1) : d318162 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d316161, d317341, d318162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83882 q ha hb
    | true =>
      simp only [d316161, d317341, d318162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d316162 q = 1) (hb : d317342 q = 1) : d318163 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d316162, d317342, d318163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316162, d317342, d318163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d316163 q = 1) (hb : d317343 q = 1) : d318164 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d316163, d317343, d318164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d316163, d317343, d318164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d316164 q = 1) (hb : d317344 q = 1) : d318165 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d316164, d317344, d318165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316164, d317344, d318165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d316165 q = 1) (hb : d317345 q = 1) : d318166 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d316165, d317345, d318166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316165, d317345, d318166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d316166 q = 1) (hb : d317346 q = 1) : d318167 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d316166, d317346, d318167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316166, d317346, d318167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83884 (p : Pattern) (ha : d316172 p = 1) (hb : d317352 p = 1) : d318173 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315925 q = 1) (hb : d317133 q = 1) : d318013 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d315925, d317133, d318013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315925, d317133, d318013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83840 q ha hb
  have h2 (q : Pattern) (ha : d315926 q = 1) (hb : d317134 q = 1) : d318014 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d315926, d317134, d318014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d315926, d317134, d318014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d315935 q = 1) (hb : d317143 q = 1) : d318023 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d315935, d317143, d318023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83840 q ha hb
    | true =>
      simp only [d315935, d317143, d318023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83843 q ha hb
  have h4 (q : Pattern) (ha : d315936 q = 1) (hb : d317144 q = 1) : d318024 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d315936, d317144, d318024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315936, d317144, d318024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d315937 q = 1) (hb : d317145 q = 1) : d318025 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d315937, d317145, d318025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315937, d317145, d318025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d316030 q = 1) (hb : d317221 q = 1) : d318084 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d316030, d317221, d318084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83857 q ha hb
    | true =>
      simp only [d316030, d317221, d318084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83865 q ha hb
  have h7 (q : Pattern) (ha : d316043 q = 1) (hb : d317239 q = 1) : d318097 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d316043, d317239, d318097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83866 q ha hb
    | true =>
      simp only [d316043, d317239, d318097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83867 q ha hb
  have h8 (q : Pattern) (ha : d316044 q = 1) (hb : d317240 q = 1) : d318098 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d316044, d317240, d318098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d316044, d317240, d318098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d316045 q = 1) (hb : d317241 q = 1) : d318099 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d316045, d317241, d318099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d316045, d317241, d318099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d316046 q = 1) (hb : d317242 q = 1) : d318100 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d316046, d317242, d318100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316046, d317242, d318100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d316050 q = 1) (hb : d317246 q = 1) : d318104 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d316050, d317246, d318104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316050, d317246, d318104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83868 q ha hb
  have h12 (q : Pattern) (ha : d316052 q = 1) (hb : d317248 q = 1) : d318106 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d316052, d317248, d318106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316052, d317248, d318106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83869 q ha hb
  have h13 (q : Pattern) (ha : d316053 q = 1) (hb : d317249 q = 1) : d318107 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d316053, d317249, d318107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d316053, d317249, d318107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d316054 q = 1) (hb : d317250 q = 1) : d318108 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d316054, d317250, d318108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d316054, d317250, d318108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d316055 q = 1) (hb : d317251 q = 1) : d318109 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d316055, d317251, d318109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d316055, d317251, d318109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d316056 q = 1) (hb : d317252 q = 1) : d318110 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d316056, d317252, d318110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d316056, d317252, d318110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d316160 q = 1) (hb : d317336 q = 1) : d318157 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d316160, d317336, d318157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316160, d317336, d318157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83881 q ha hb
  have h18 (q : Pattern) (ha : d316167 q = 1) (hb : d317347 q = 1) : d318168 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d316167, d317347, d318168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316167, d317347, d318168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83883 q ha hb
  have h19 (q : Pattern) (ha : d316168 q = 1) (hb : d317348 q = 1) : d318169 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d316168, d317348, d318169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d316168, d317348, d318169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d316169 q = 1) (hb : d317349 q = 1) : d318170 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d316169, d317349, d318170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d316169, d317349, d318170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d316170 q = 1) (hb : d317350 q = 1) : d318171 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d316170, d317350, d318171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d316170, d317350, d318171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d316171 q = 1) (hb : d317351 q = 1) : d318172 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d316171, d317351, d318172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d316171, d317351, d318172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d316172 q = 1) (hb : d317352 q = 1) : d318173 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d316172, d317352, d318173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d316172, d317352, d318173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro83885 (p : Pattern) (ha : d316178 p = 1) (hb : d317358 p = 1) : d318179 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316173 q = 1) (hb : d317353 q = 1) : d318174 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d316173, d317353, d318174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316173, d317353, d318174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83884 q ha hb
  have h2 (q : Pattern) (ha : d316174 q = 1) (hb : d317354 q = 1) : d318175 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d316174, d317354, d318175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316174, d317354, d318175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d316175 q = 1) (hb : d317355 q = 1) : d318176 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d316175, d317355, d318176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316175, d317355, d318176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d316176 q = 1) (hb : d317356 q = 1) : d318177 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d316176, d317356, d318177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316176, d317356, d318177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d316177 q = 1) (hb : d317357 q = 1) : d318178 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d316177, d317357, d318178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316177, d317357, d318178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d316178 q = 1) (hb : d317358 q = 1) : d318179 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d316178, d317358, d318179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316178, d317358, d318179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83886 (p : Pattern) (ha : d316184 p = 1) (hb : d317364 p = 1) : d318185 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d316506 q = 1) : d316506 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d315486 q = 1) (hb : d316764 q = 1) : d317688 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d315486, d316764, d317688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d315486, d316764, d317688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83768 q ha hb
  have h3 (q : Pattern) (ha : d315487 q = 1) (hb : d316765 q = 1) : d317689 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d315487, d316765, d317689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d315487, d316765, d317689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315488 q = 1) (hb : d316766 q = 1) : d317690 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d315488, d316766, d317690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d315488, d316766, d317690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315845 q = 1) (hb : d317059 q = 1) : d317972 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d315845, d317059, d317972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d315845, d317059, d317972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83830 q ha hb
  have h6 (q : Pattern) (ha : d315846 q = 1) (hb : d317060 q = 1) : d317973 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d315846, d317060, d317973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d315846, d317060, d317973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d315847 q = 1) (hb : d317061 q = 1) : d317974 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d315847, d317061, d317974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d315847, d317061, d317974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d315848 q = 1) (hb : d317062 q = 1) : d317975 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d315848, d317062, d317975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315848, d317062, d317975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d316179 q = 1) (hb : d317359 q = 1) : d318180 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d316179, d317359, d318180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d316179, d317359, d318180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83885 q ha hb
  have h10 (q : Pattern) (ha : d316180 q = 1) (hb : d317360 q = 1) : d318181 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d316180, d317360, d318181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d316180, d317360, d318181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d316181 q = 1) (hb : d317361 q = 1) : d318182 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d316181, d317361, d318182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d316181, d317361, d318182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d316182 q = 1) (hb : d317362 q = 1) : d318183 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d316182, d317362, d318183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d316182, d317362, d318183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d316183 q = 1) (hb : d317363 q = 1) : d318184 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d316183, d317363, d318184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d316183, d317363, d318184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d316184 q = 1) (hb : d317364 q = 1) : d318185 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d316184, d317364, d318185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d316184, d317364, d318185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h14 p ha hb
theorem andIntro83887 (p : Pattern) (ha : d316190 p = 1) (hb : d317370 p = 1) : d318191 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316185 q = 1) (hb : d317365 q = 1) : d318186 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d316185, d317365, d318186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83886 q ha hb
    | true =>
      simp only [d316185, d317365, d318186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d316186 q = 1) (hb : d317366 q = 1) : d318187 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d316186, d317366, d318187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d316186, d317366, d318187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d316187 q = 1) (hb : d317367 q = 1) : d318188 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d316187, d317367, d318188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d316187, d317367, d318188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d316188 q = 1) (hb : d317368 q = 1) : d318189 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d316188, d317368, d318189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d316188, d317368, d318189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d316189 q = 1) (hb : d317369 q = 1) : d318190 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d316189, d317369, d318190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d316189, d317369, d318190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d316190 q = 1) (hb : d317370 q = 1) : d318191 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d316190, d317370, d318191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316190, d317370, d318191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83888 (p : Pattern) (ha : d316196 p = 1) (hb : d317376 p = 1) : d318197 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316191 q = 1) (hb : d317371 q = 1) : d318192 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d316191, d317371, d318192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83887 q ha hb
    | true =>
      simp only [d316191, d317371, d318192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d316192 q = 1) (hb : d317372 q = 1) : d318193 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d316192, d317372, d318193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d316192, d317372, d318193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d316193 q = 1) (hb : d317373 q = 1) : d318194 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d316193, d317373, d318194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d316193, d317373, d318194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d316194 q = 1) (hb : d317374 q = 1) : d318195 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d316194, d317374, d318195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d316194, d317374, d318195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d316195 q = 1) (hb : d317375 q = 1) : d318196 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d316195, d317375, d318196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d316195, d317375, d318196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d316196 q = 1) (hb : d317376 q = 1) : d318197 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d316196, d317376, d318197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316196, d317376, d318197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83889 (p : Pattern) (ha : d316202 p = 1) (hb : d317382 p = 1) : d318203 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316197 q = 1) (hb : d317377 q = 1) : d318198 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d316197, d317377, d318198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83888 q ha hb
    | true =>
      simp only [d316197, d317377, d318198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d316198 q = 1) (hb : d317378 q = 1) : d318199 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d316198, d317378, d318199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d316198, d317378, d318199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d316199 q = 1) (hb : d317379 q = 1) : d318200 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d316199, d317379, d318200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d316199, d317379, d318200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d316200 q = 1) (hb : d317380 q = 1) : d318201 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d316200, d317380, d318201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d316200, d317380, d318201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d316201 q = 1) (hb : d317381 q = 1) : d318202 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d316201, d317381, d318202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d316201, d317381, d318202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d316202 q = 1) (hb : d317382 q = 1) : d318203 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d316202, d317382, d318203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316202, d317382, d318203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83890 (p : Pattern) (ha : d316208 p = 1) (hb : d317388 p = 1) : d318209 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316203 q = 1) (hb : d317383 q = 1) : d318204 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d316203, d317383, d318204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83889 q ha hb
    | true =>
      simp only [d316203, d317383, d318204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d316204 q = 1) (hb : d317384 q = 1) : d318205 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d316204, d317384, d318205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d316204, d317384, d318205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d316205 q = 1) (hb : d317385 q = 1) : d318206 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d316205, d317385, d318206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d316205, d317385, d318206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d316206 q = 1) (hb : d317386 q = 1) : d318207 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d316206, d317386, d318207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d316206, d317386, d318207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d316207 q = 1) (hb : d317387 q = 1) : d318208 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d316207, d317387, d318208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d316207, d317387, d318208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d316208 q = 1) (hb : d317388 q = 1) : d318209 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d316208, d317388, d318209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316208, d317388, d318209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83891 (p : Pattern) (ha : d316214 p = 1) (hb : d317394 p = 1) : d318215 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316209 q = 1) (hb : d317389 q = 1) : d318210 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d316209, d317389, d318210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83890 q ha hb
    | true =>
      simp only [d316209, d317389, d318210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d316210 q = 1) (hb : d317390 q = 1) : d318211 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d316210, d317390, d318211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d316210, d317390, d318211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d316211 q = 1) (hb : d317391 q = 1) : d318212 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d316211, d317391, d318212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d316211, d317391, d318212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d316212 q = 1) (hb : d317392 q = 1) : d318213 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d316212, d317392, d318213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d316212, d317392, d318213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d316213 q = 1) (hb : d317393 q = 1) : d318214 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d316213, d317393, d318214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d316213, d317393, d318214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d316214 q = 1) (hb : d317394 q = 1) : d318215 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d316214, d317394, d318215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316214, d317394, d318215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83892 (p : Pattern) (ha : d316220 p = 1) (hb : d317400 p = 1) : d318221 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316215 q = 1) (hb : d317395 q = 1) : d318216 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d316215, d317395, d318216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83891 q ha hb
    | true =>
      simp only [d316215, d317395, d318216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d316216 q = 1) (hb : d317396 q = 1) : d318217 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d316216, d317396, d318217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d316216, d317396, d318217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d316217 q = 1) (hb : d317397 q = 1) : d318218 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d316217, d317397, d318218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d316217, d317397, d318218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d316218 q = 1) (hb : d317398 q = 1) : d318219 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d316218, d317398, d318219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d316218, d317398, d318219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d316219 q = 1) (hb : d317399 q = 1) : d318220 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d316219, d317399, d318220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d316219, d317399, d318220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d316220 q = 1) (hb : d317400 q = 1) : d318221 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d316220, d317400, d318221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316220, d317400, d318221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83893 (p : Pattern) (ha : d316226 p = 1) (hb : d317406 p = 1) : d318227 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316221 q = 1) (hb : d317401 q = 1) : d318222 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d316221, d317401, d318222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83892 q ha hb
    | true =>
      simp only [d316221, d317401, d318222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d316222 q = 1) (hb : d317402 q = 1) : d318223 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d316222, d317402, d318223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d316222, d317402, d318223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d316223 q = 1) (hb : d317403 q = 1) : d318224 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d316223, d317403, d318224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d316223, d317403, d318224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d316224 q = 1) (hb : d317404 q = 1) : d318225 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d316224, d317404, d318225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d316224, d317404, d318225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d316225 q = 1) (hb : d317405 q = 1) : d318226 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d316225, d317405, d318226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d316225, d317405, d318226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d316226 q = 1) (hb : d317406 q = 1) : d318227 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d316226, d317406, d318227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316226, d317406, d318227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83894 (p : Pattern) (ha : d282284 p = 1) (hb : d312377 p = 1) : d257490 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33246 q = 1) (hb : d282284 q = 1) : d257214 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33246, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83365 q ha hb
    | true =>
      simp only [d33246, d257214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72056 q ha hb
  have h2 (q : Pattern) (ha : d33306 q = 1) (hb : d282284 q = 1) : d257272 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33306, d257272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33306, d257272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33307 q = 1) (hb : d282284 q = 1) : d257273 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33307, d257273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33307, d257273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33308 q = 1) (hb : d282284 q = 1) : d257274 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33308, d257274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33308, d257274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33309 q = 1) (hb : d282284 q = 1) : d257275 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33309, d257275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33309, d257275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d282284 q = 1) (hb : d312377 q = 1) : d257490 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312377, d257490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312377, d257490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro83895 (p : Pattern) (ha : d282284 p = 1) (hb : d312387 p = 1) : d257536 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33282 q = 1) (hb : d282284 q = 1) : d257248 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33282, d257248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83370 q ha hb
    | true =>
      simp only [d33282, d257248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72061 q ha hb
  have h2 (q : Pattern) (ha : d282284 q = 1) (hb : d312383 q = 1) : d257532 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d312383, d257532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312383, d257532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d282284 q = 1) (hb : d312384 q = 1) : d257533 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d312384, d257533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312384, d257533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d282284 q = 1) (hb : d312385 q = 1) : d257534 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d312385, d257534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312385, d257534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d282284 q = 1) (hb : d312386 q = 1) : d257535 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d312386, d257535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312386, d257535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d282284 q = 1) (hb : d312387 q = 1) : d257536 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312387, d257536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312387, d257536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83896 (p : Pattern) (ha : d282284 p = 1) (hb : d312393 p = 1) : d259893 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33311 q = 1) (hb : d282284 q = 1) : d257277 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d33311, d257277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83373 q ha hb
    | true =>
      simp only [d33311, d257277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83374 q ha hb
  have h2 (q : Pattern) (ha : d33312 q = 1) (hb : d282284 q = 1) : d257278 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d33312, d257278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33312, d257278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d282284 q = 1) (hb : d312375 q = 1) : d259883 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312375, d259883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d312375, d259883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d282284 q = 1) (hb : d312376 q = 1) : d259884 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312376, d259884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312376, d259884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d282284 q = 1) (hb : d312378 q = 1) : d257491 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312378, d257491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312378, d257491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83894 q ha hb
  have h6 (q : Pattern) (ha : d282284 q = 1) (hb : d312379 q = 1) : d259885 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312379, d259885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312379, d259885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d282284 q = 1) (hb : d312380 q = 1) : d259886 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312380, d259886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d312380, d259886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d282284 q = 1) (hb : d312381 q = 1) : d259887 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312381, d259887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d312381, d259887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d282284 q = 1) (hb : d312382 q = 1) : d259888 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312382, d259888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312382, d259888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d282284 q = 1) (hb : d312388 q = 1) : d257537 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312388, d257537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312388, d257537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83895 q ha hb
  have h11 (q : Pattern) (ha : d282284 q = 1) (hb : d312389 q = 1) : d259889 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312389, d259889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d312389, d259889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d282284 q = 1) (hb : d312390 q = 1) : d259890 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312390, d259890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d312390, d259890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d282284 q = 1) (hb : d312391 q = 1) : d259891 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312391, d259891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d312391, d259891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d282284 q = 1) (hb : d312392 q = 1) : d259892 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312392, d259892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d312392, d259892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d282284 q = 1) (hb : d312393 q = 1) : d259893 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d312393, d259893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d312393, d259893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro83897 (p : Pattern) (ha : d282284 p = 1) (hb : d312399 p = 1) : d259899 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72707 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d282284 q = 1) (hb : d312394 q = 1) : d259894 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d312394, d259894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312394, d259894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83896 q ha hb
  have h7 (q : Pattern) (ha : d282284 q = 1) (hb : d312395 q = 1) : d259895 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d312395, d259895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312395, d259895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d282284 q = 1) (hb : d312396 q = 1) : d259896 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d312396, d259896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312396, d259896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d282284 q = 1) (hb : d312397 q = 1) : d259897 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d312397, d259897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312397, d259897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d282284 q = 1) (hb : d312398 q = 1) : d259898 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d312398, d259898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312398, d259898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d282284 q = 1) (hb : d312399 q = 1) : d259899 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d312399, d259899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d312399, d259899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro83898 (p : Pattern) (ha : d282284 p = 1) (hb : d312402 p = 1) : d287253 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33527 q = 1) (hb : d282284 q = 1) : d285897 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33527, d285897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83404 q ha hb
    | true =>
      simp only [d33527, d285897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83405 q ha hb
  have h2 (q : Pattern) (ha : d33528 q = 1) (hb : d282284 q = 1) : d285958 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33528, d285958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33528, d285958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33529 q = 1) (hb : d282284 q = 1) : d285959 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33529, d285959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33529, d285959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33530 q = 1) (hb : d282284 q = 1) : d285960 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33530, d285960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33530, d285960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33531 q = 1) (hb : d282284 q = 1) : d285961 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33531, d285961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33531, d285961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d282284 q = 1) (hb : d312402 q = 1) : d287253 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312402, d287253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312402, d287253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro83899 (p : Pattern) (ha : d282284 p = 1) (hb : d312413 p = 1) : d287263 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d282284 q = 1) (hb : d312408 q = 1) : d285933 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d312408, d285933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83441 q hb ha
    | true =>
      simp only [d312408, d285933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83411 q hb ha
  have h2 (q : Pattern) (ha : d282284 q = 1) (hb : d312409 q = 1) : d287259 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d312409, d287259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312409, d287259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d282284 q = 1) (hb : d312410 q = 1) : d287260 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d312410, d287260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312410, d287260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d282284 q = 1) (hb : d312411 q = 1) : d287261 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d312411, d287261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312411, d287261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d282284 q = 1) (hb : d312412 q = 1) : d287262 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d312412, d287262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312412, d287262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d282284 q = 1) (hb : d312413 q = 1) : d287263 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312413, d287263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312413, d287263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83900 (p : Pattern) (ha : d282284 p = 1) (hb : d312419 p = 1) : d287269 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33533 q = 1) (hb : d282284 q = 1) : d285963 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d33533, d285963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83403 q ha hb
    | true =>
      simp only [d33533, d285963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83406 q ha hb
  have h2 (q : Pattern) (ha : d33534 q = 1) (hb : d282284 q = 1) : d285964 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d33534, d285964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33534, d285964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d282284 q = 1) (hb : d312400 q = 1) : d287251 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312400, d287251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d312400, d287251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d282284 q = 1) (hb : d312401 q = 1) : d287252 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312401, d287252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312401, d287252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d282284 q = 1) (hb : d312403 q = 1) : d287254 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312403, d287254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312403, d287254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83898 q ha hb
  have h6 (q : Pattern) (ha : d282284 q = 1) (hb : d312404 q = 1) : d287255 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312404, d287255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312404, d287255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d282284 q = 1) (hb : d312405 q = 1) : d287256 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312405, d287256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d312405, d287256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d282284 q = 1) (hb : d312406 q = 1) : d287257 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312406, d287257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d312406, d287257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d282284 q = 1) (hb : d312407 q = 1) : d287258 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312407, d287258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312407, d287258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d282284 q = 1) (hb : d312414 q = 1) : d287264 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312414, d287264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312414, d287264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83899 q ha hb
  have h11 (q : Pattern) (ha : d282284 q = 1) (hb : d312415 q = 1) : d287265 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312415, d287265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d312415, d287265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d282284 q = 1) (hb : d312416 q = 1) : d287266 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312416, d287266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d312416, d287266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d282284 q = 1) (hb : d312417 q = 1) : d287267 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312417, d287267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d312417, d287267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d282284 q = 1) (hb : d312418 q = 1) : d287268 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312418, d287268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d312418, d287268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d282284 q = 1) (hb : d312419 q = 1) : d287269 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d312419, d287269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d312419, d287269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro83901 (p : Pattern) (ha : d282284 p = 1) (hb : d312425 p = 1) : d287275 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d282284 q = 1) (hb : d312420 q = 1) : d287270 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d312420, d287270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312420, d287270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83900 q ha hb
  have h2 (q : Pattern) (ha : d282284 q = 1) (hb : d312421 q = 1) : d287271 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d312421, d287271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312421, d287271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d282284 q = 1) (hb : d312422 q = 1) : d287272 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d312422, d287272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312422, d287272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d282284 q = 1) (hb : d312423 q = 1) : d287273 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d312423, d287273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312423, d287273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d282284 q = 1) (hb : d312424 q = 1) : d287274 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d312424, d287274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312424, d287274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d282284 q = 1) (hb : d312425 q = 1) : d287275 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d312425, d287275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312425, d287275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83902 (p : Pattern) (ha : d282284 p = 1) (hb : d312429 p = 1) : d318230 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33867 q = 1) (hb : d282284 q = 1) : d316332 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33867, d316332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83455 q ha hb
    | true =>
      simp only [d33867, d316332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83456 q ha hb
  have h2 (q : Pattern) (ha : d33868 q = 1) (hb : d282284 q = 1) : d316333 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33868, d316333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33868, d316333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33869 q = 1) (hb : d282284 q = 1) : d316334 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33869, d316334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33869, d316334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33870 q = 1) (hb : d282284 q = 1) : d316335 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33870, d316335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33870, d316335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33871 q = 1) (hb : d282284 q = 1) : d316336 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33871, d316336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33871, d316336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d282284 q = 1) (hb : d312429 q = 1) : d318230 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312429, d318230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312429, d318230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro83903 (p : Pattern) (ha : d282284 p = 1) (hb : d312440 p = 1) : d318241 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d282284 q = 1) (hb : d312435 q = 1) : d318236 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d312435, d318236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83496 q hb ha
    | true =>
      simp only [d312435, d318236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83464 q hb ha
  have h2 (q : Pattern) (ha : d282284 q = 1) (hb : d312436 q = 1) : d318237 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d312436, d318237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312436, d318237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d282284 q = 1) (hb : d312437 q = 1) : d318238 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d312437, d318238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312437, d318238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d282284 q = 1) (hb : d312438 q = 1) : d318239 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d312438, d318239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312438, d318239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d282284 q = 1) (hb : d312439 q = 1) : d318240 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d312439, d318240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312439, d318240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d282284 q = 1) (hb : d312440 q = 1) : d318241 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312440, d318241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312440, d318241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83904 (p : Pattern) (ha : d282284 p = 1) (hb : d312446 p = 1) : d318247 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33873 q = 1) (hb : d282284 q = 1) : d316338 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d33873, d316338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83454 q ha hb
    | true =>
      simp only [d33873, d316338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83457 q ha hb
  have h2 (q : Pattern) (ha : d33874 q = 1) (hb : d282284 q = 1) : d316339 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d33874, d316339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33874, d316339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d282284 q = 1) (hb : d312427 q = 1) : d318228 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312427, d318228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d312427, d318228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d282284 q = 1) (hb : d312428 q = 1) : d318229 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312428, d318229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312428, d318229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d282284 q = 1) (hb : d312430 q = 1) : d318231 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312430, d318231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312430, d318231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83902 q ha hb
  have h6 (q : Pattern) (ha : d282284 q = 1) (hb : d312431 q = 1) : d318232 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312431, d318232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312431, d318232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d282284 q = 1) (hb : d312432 q = 1) : d318233 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312432, d318233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d312432, d318233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d282284 q = 1) (hb : d312433 q = 1) : d318234 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312433, d318234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d312433, d318234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d282284 q = 1) (hb : d312434 q = 1) : d318235 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312434, d318235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312434, d318235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d282284 q = 1) (hb : d312441 q = 1) : d318242 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312441, d318242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312441, d318242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83903 q ha hb
  have h11 (q : Pattern) (ha : d282284 q = 1) (hb : d312442 q = 1) : d318243 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312442, d318243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d312442, d318243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d282284 q = 1) (hb : d312443 q = 1) : d318244 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312443, d318244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d312443, d318244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d282284 q = 1) (hb : d312444 q = 1) : d318245 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312444, d318245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d312444, d318245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d282284 q = 1) (hb : d312445 q = 1) : d318246 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312445, d318246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d312445, d318246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d282284 q = 1) (hb : d312446 q = 1) : d318247 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d312446, d318247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d312446, d318247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro83905 (p : Pattern) (ha : d282284 p = 1) (hb : d312452 p = 1) : d318253 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d282284 q = 1) (hb : d312447 q = 1) : d318248 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d312447, d318248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312447, d318248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83904 q ha hb
  have h2 (q : Pattern) (ha : d282284 q = 1) (hb : d312448 q = 1) : d318249 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d312448, d318249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312448, d318249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d282284 q = 1) (hb : d312449 q = 1) : d318250 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d312449, d318250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312449, d318250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d282284 q = 1) (hb : d312450 q = 1) : d318251 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d312450, d318251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312450, d318251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d282284 q = 1) (hb : d312451 q = 1) : d318252 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d312451, d318252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312451, d318252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d282284 q = 1) (hb : d312452 q = 1) : d318253 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d312452, d318253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312452, d318253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83906 (p : Pattern) (ha : d282284 p = 1) (hb : d312457 p = 1) : d318258 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34326 q = 1) (hb : d282284 q = 1) : d316545 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d34326, d316545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83516 q ha hb
    | true =>
      simp only [d34326, d316545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83517 q ha hb
  have h2 (q : Pattern) (ha : d34327 q = 1) (hb : d282284 q = 1) : d316546 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d34327, d316546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34327, d316546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d34328 q = 1) (hb : d282284 q = 1) : d316547 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d34328, d316547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d34328, d316547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d34329 q = 1) (hb : d282284 q = 1) : d316548 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d34329, d316548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34329, d316548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d34330 q = 1) (hb : d282284 q = 1) : d316549 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d34330, d316549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34330, d316549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d282284 q = 1) (hb : d312457 q = 1) : d318258 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312457, d318258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312457, d318258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro83907 (p : Pattern) (ha : d282284 p = 1) (hb : d312468 p = 1) : d318269 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d282284 q = 1) (hb : d312463 q = 1) : d318264 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d312463, d318264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83558 q hb ha
    | true =>
      simp only [d312463, d318264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83525 q hb ha
  have h2 (q : Pattern) (ha : d282284 q = 1) (hb : d312464 q = 1) : d318265 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d312464, d318265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312464, d318265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d282284 q = 1) (hb : d312465 q = 1) : d318266 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d312465, d318266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312465, d318266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d282284 q = 1) (hb : d312466 q = 1) : d318267 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d312466, d318267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312466, d318267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d282284 q = 1) (hb : d312467 q = 1) : d318268 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d312467, d318268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312467, d318268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d282284 q = 1) (hb : d312468 q = 1) : d318269 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312468, d318269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312468, d318269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83908 (p : Pattern) (ha : d282284 p = 1) (hb : d312474 p = 1) : d318275 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34332 q = 1) (hb : d282284 q = 1) : d316551 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d34332, d316551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83515 q ha hb
    | true =>
      simp only [d34332, d316551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83518 q ha hb
  have h2 (q : Pattern) (ha : d34333 q = 1) (hb : d282284 q = 1) : d316552 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d34333, d316552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d34333, d316552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d282284 q = 1) (hb : d312455 q = 1) : d318256 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312455, d318256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d312455, d318256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d282284 q = 1) (hb : d312456 q = 1) : d318257 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312456, d318257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312456, d318257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d282284 q = 1) (hb : d312458 q = 1) : d318259 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312458, d318259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312458, d318259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83906 q ha hb
  have h6 (q : Pattern) (ha : d282284 q = 1) (hb : d312459 q = 1) : d318260 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312459, d318260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312459, d318260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d282284 q = 1) (hb : d312460 q = 1) : d318261 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312460, d318261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d312460, d318261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d282284 q = 1) (hb : d312461 q = 1) : d318262 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312461, d318262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d312461, d318262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d282284 q = 1) (hb : d312462 q = 1) : d318263 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312462, d318263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312462, d318263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d282284 q = 1) (hb : d312469 q = 1) : d318270 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312469, d318270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312469, d318270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83907 q ha hb
  have h11 (q : Pattern) (ha : d282284 q = 1) (hb : d312470 q = 1) : d318271 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312470, d318271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d312470, d318271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d282284 q = 1) (hb : d312471 q = 1) : d318272 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312471, d318272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d312471, d318272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d282284 q = 1) (hb : d312472 q = 1) : d318273 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312472, d318273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d312472, d318273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d282284 q = 1) (hb : d312473 q = 1) : d318274 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312473, d318274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d312473, d318274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d282284 q = 1) (hb : d312474 q = 1) : d318275 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d312474, d318275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d312474, d318275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro83909 (p : Pattern) (ha : d282284 p = 1) (hb : d312480 p = 1) : d318281 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d282284 q = 1) (hb : d312475 q = 1) : d318276 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d312475, d318276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312475, d318276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83908 q ha hb
  have h2 (q : Pattern) (ha : d282284 q = 1) (hb : d312476 q = 1) : d318277 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d312476, d318277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312476, d318277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d282284 q = 1) (hb : d312477 q = 1) : d318278 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d312477, d318278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312477, d318278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d282284 q = 1) (hb : d312478 q = 1) : d318279 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d312478, d318279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312478, d318279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d282284 q = 1) (hb : d312479 q = 1) : d318280 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d312479, d318280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312479, d318280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d282284 q = 1) (hb : d312480 q = 1) : d318281 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d312480, d318281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312480, d318281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83910 (p : Pattern) (ha : d282284 p = 1) (hb : d312486 p = 1) : d318287 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34892 q = 1) (hb : d282284 q = 1) : d316832 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d34892, d316832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83581 q ha hb
    | true =>
      simp only [d34892, d316832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83582 q ha hb
  have h2 (q : Pattern) (ha : d34893 q = 1) (hb : d282284 q = 1) : d316833 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d34893, d316833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34893, d316833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d34894 q = 1) (hb : d282284 q = 1) : d316834 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d34894, d316834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d34894, d316834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d34895 q = 1) (hb : d282284 q = 1) : d316835 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d34895, d316835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34895, d316835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d34896 q = 1) (hb : d282284 q = 1) : d316836 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d34896, d316836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d34896, d316836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d282284 q = 1) (hb : d312486 q = 1) : d318287 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312486, d318287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312486, d318287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro83911 (p : Pattern) (ha : d282284 p = 1) (hb : d312497 p = 1) : d318298 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d282284 q = 1) (hb : d312492 q = 1) : d318293 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d312492, d318293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83625 q hb ha
    | true =>
      simp only [d312492, d318293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83590 q hb ha
  have h2 (q : Pattern) (ha : d282284 q = 1) (hb : d312493 q = 1) : d318294 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d312493, d318294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312493, d318294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d282284 q = 1) (hb : d312494 q = 1) : d318295 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d312494, d318295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312494, d318295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d282284 q = 1) (hb : d312495 q = 1) : d318296 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d312495, d318296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312495, d318296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d282284 q = 1) (hb : d312496 q = 1) : d318297 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d312496, d318297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312496, d318297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d282284 q = 1) (hb : d312497 q = 1) : d318298 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312497, d318298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312497, d318298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83912 (p : Pattern) (ha : d282284 p = 1) (hb : d312503 p = 1) : d318304 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34898 q = 1) (hb : d282284 q = 1) : d316838 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d34898, d316838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83580 q ha hb
    | true =>
      simp only [d34898, d316838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83583 q ha hb
  have h2 (q : Pattern) (ha : d34899 q = 1) (hb : d282284 q = 1) : d316839 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d34899, d316839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d34899, d316839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d282284 q = 1) (hb : d312484 q = 1) : d318285 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312484, d318285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d312484, d318285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d282284 q = 1) (hb : d312485 q = 1) : d318286 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312485, d318286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312485, d318286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d282284 q = 1) (hb : d312487 q = 1) : d318288 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312487, d318288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312487, d318288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83910 q ha hb
  have h6 (q : Pattern) (ha : d282284 q = 1) (hb : d312488 q = 1) : d318289 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312488, d318289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312488, d318289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d282284 q = 1) (hb : d312489 q = 1) : d318290 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312489, d318290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d312489, d318290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d282284 q = 1) (hb : d312490 q = 1) : d318291 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312490, d318291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d312490, d318291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d282284 q = 1) (hb : d312491 q = 1) : d318292 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312491, d318292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312491, d318292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d282284 q = 1) (hb : d312498 q = 1) : d318299 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312498, d318299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312498, d318299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83911 q ha hb
  have h11 (q : Pattern) (ha : d282284 q = 1) (hb : d312499 q = 1) : d318300 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312499, d318300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d312499, d318300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d282284 q = 1) (hb : d312500 q = 1) : d318301 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312500, d318301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d312500, d318301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d282284 q = 1) (hb : d312501 q = 1) : d318302 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312501, d318302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d312501, d318302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d282284 q = 1) (hb : d312502 q = 1) : d318303 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312502, d318303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d312502, d318303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d282284 q = 1) (hb : d312503 q = 1) : d318304 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d312503, d318304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d312503, d318304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro83913 (p : Pattern) (ha : d282284 p = 1) (hb : d312509 p = 1) : d318310 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d282284 q = 1) (hb : d312504 q = 1) : d318305 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d312504, d318305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312504, d318305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83912 q ha hb
  have h2 (q : Pattern) (ha : d282284 q = 1) (hb : d312505 q = 1) : d318306 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d312505, d318306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312505, d318306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d282284 q = 1) (hb : d312506 q = 1) : d318307 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d312506, d318307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312506, d318307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d282284 q = 1) (hb : d312507 q = 1) : d318308 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d312507, d318308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312507, d318308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d282284 q = 1) (hb : d312508 q = 1) : d318309 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d312508, d318309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312508, d318309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d282284 q = 1) (hb : d312509 q = 1) : d318310 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d312509, d318310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312509, d318310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83914 (p : Pattern) (ha : d282284 p = 1) (hb : d312516 p = 1) : d318317 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d35475 q = 1) (hb : d282284 q = 1) : d317137 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d35475, d317137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83652 q ha hb
    | true =>
      simp only [d35475, d317137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83653 q ha hb
  have h2 (q : Pattern) (ha : d35476 q = 1) (hb : d282284 q = 1) : d317138 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d35476, d317138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35476, d317138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d35477 q = 1) (hb : d282284 q = 1) : d317139 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d35477, d317139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d35477, d317139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d35478 q = 1) (hb : d282284 q = 1) : d317140 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d35478, d317140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35478, d317140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d35479 q = 1) (hb : d282284 q = 1) : d317141 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d35479, d317141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35479, d317141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d282284 q = 1) (hb : d312516 q = 1) : d318317 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312516, d318317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312516, d318317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro83915 (p : Pattern) (ha : d282284 p = 1) (hb : d312523 p = 1) : d317323 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d35771 q = 1) (hb : d282284 q = 1) : d317280 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d35771, d317280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83690 q ha hb
    | true =>
      simp only [d35771, d317280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83660 q ha hb
  have h2 (q : Pattern) (ha : d35772 q = 1) (hb : d282284 q = 1) : d317281 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d35772, d317281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35772, d317281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d35773 q = 1) (hb : d282284 q = 1) : d317282 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d35773, d317282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35773, d317282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d35780 q = 1) (hb : d282284 q = 1) : d317289 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d35780, d317289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83660 q ha hb
    | true =>
      simp only [d35780, d317289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83692 q ha hb
  have h5 (q : Pattern) (ha : d35781 q = 1) (hb : d282284 q = 1) : d317290 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d35781, d317290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35781, d317290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d35782 q = 1) (hb : d282284 q = 1) : d317291 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d35782, d317291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35782, d317291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d35783 q = 1) (hb : d282284 q = 1) : d317292 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d35783, d317292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d35783, d317292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d35799 q = 1) (hb : d282284 q = 1) : d317308 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d35799, d317308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83660 q ha hb
    | true =>
      simp only [d35799, d317308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83661 q ha hb
  have h9 (q : Pattern) (ha : d35800 q = 1) (hb : d282284 q = 1) : d317309 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d35800, d317309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35800, d317309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d35801 q = 1) (hb : d282284 q = 1) : d317310 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d35801, d317310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35801, d317310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d35802 q = 1) (hb : d282284 q = 1) : d317311 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d35802, d317311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d35802, d317311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d282284 q = 1) (hb : d312522 q = 1) : d317322 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d312522, d317322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d312522, d317322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d282284 q = 1) (hb : d312523 q = 1) : d317323 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d312523, d317323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d312523, d317323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro83916 (p : Pattern) (ha : d282284 p = 1) (hb : d312529 p = 1) : d318326 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d282284 q = 1) (hb : d312524 q = 1) : d317324 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d312524, d317324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83915 q ha hb
    | true =>
      simp only [d312524, d317324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d282284 q = 1) (hb : d312525 q = 1) : d317325 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d312525, d317325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312525, d317325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d35805 q = 1) (hb : d282284 q = 1) : d317314 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d35805, d317314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83662 q ha hb
    | true =>
      simp only [d35805, d317314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d35806 q = 1) (hb : d282284 q = 1) : d317315 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d35806, d317315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35806, d317315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d282284 q = 1) (hb : d312526 q = 1) : d318323 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d312526, d318323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312526, d318323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d282284 q = 1) (hb : d312527 q = 1) : d318324 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d312527, d318324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312527, d318324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d282284 q = 1) (hb : d312528 q = 1) : d318325 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d312528, d318325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d312528, d318325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d282284 q = 1) (hb : d312529 q = 1) : d318326 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d312529, d318326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d312529, d318326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro83917 (p : Pattern) (ha : d282284 p = 1) (hb : d312535 p = 1) : d318331 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282283 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2040 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2058 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2058, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2058, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d258695 q = 1) (hb : d282283 q = 1) : d258695 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d2042 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d282284 q = 1) (hb : d312530 q = 1) : d258696 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d282284, d312530, d258696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d282284, d312530, d258696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d282284 q = 1) (hb : d312531 q = 1) : d318327 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d312531, d318327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d312531, d318327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d282284 q = 1) (hb : d312532 q = 1) : d318328 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d312532, d318328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d312532, d318328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d10405 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10405, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72349 q ha hb
    | true =>
      simp only [d10405, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10406 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10406, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72350 q ha hb
    | true =>
      simp only [d10406, d282284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h12 (q : Pattern) (ha : d10407 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10408 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h14 (q : Pattern) (ha : d282284 q = 1) (hb : d312533 q = 1) : d318329 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d312533, d318329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d312533, d318329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d282284 q = 1) (hb : d312534 q = 1) : d318330 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d312534, d318330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d312534, d318330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h16 (q : Pattern) (ha : d282284 q = 1) (hb : d312535 q = 1) : d318331 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d312535, d318331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d312535, d318331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h16 p ha hb
theorem andIntro83918 (p : Pattern) (ha : d282284 p = 1) (hb : d312541 p = 1) : d318337 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d35765 q = 1) (hb : d282284 q = 1) : d317274 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d35765, d317274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35765, d317274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83641 q ha hb
  have h2 (q : Pattern) (ha : d35417 q = 1) (hb : d282284 q = 1) : d317085 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d35417, d317085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83641 q ha hb
    | true =>
      simp only [d35417, d317085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d35766 q = 1) (hb : d282284 q = 1) : d317275 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d35766, d317275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d35766, d317275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d35418 q = 1) (hb : d282284 q = 1) : d317086 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d35418, d317086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d35418, d317086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d35767 q = 1) (hb : d282284 q = 1) : d317276 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d35767, d317276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d35767, d317276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d35768 q = 1) (hb : d282284 q = 1) : d317277 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d35768, d317277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d35768, d317277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d35797 q = 1) (hb : d282284 q = 1) : d317306 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d35797, d317306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d35797, d317306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15790 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83643 q ha hb
  have h9 (q : Pattern) (ha : d10412 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83643 q ha hb
    | true =>
      simp only [d10412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15791 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d282284 q = 1) (hb : d312536 q = 1) : d318332 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d312536, d318332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83917 q ha hb
    | true =>
      simp only [d312536, d318332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d282284 q = 1) (hb : d312537 q = 1) : d318333 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d312537, d318333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d312537, d318333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d282284 q = 1) (hb : d312538 q = 1) : d318334 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d312538, d318334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d312538, d318334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d282284 q = 1) (hb : d312539 q = 1) : d318335 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d312539, d318335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d312539, d318335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d282284 q = 1) (hb : d312540 q = 1) : d318336 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d312540, d318336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d312540, d318336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d282284 q = 1) (hb : d312541 q = 1) : d318337 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d312541, d318337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d312541, d318337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro83919 (p : Pattern) (ha : d282284 p = 1) (hb : d312547 p = 1) : d318343 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d282284 q = 1) (hb : d312542 q = 1) : d318338 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d312542, d318338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83660 q hb ha
    | true =>
      simp only [d312542, d318338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83918 q ha hb
  have h2 (q : Pattern) (ha : d282284 q = 1) (hb : d312543 q = 1) : d318339 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d312543, d318339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312543, d318339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d282284 q = 1) (hb : d312544 q = 1) : d318340 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d312544, d318340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312544, d318340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d282284 q = 1) (hb : d312545 q = 1) : d318341 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d312545, d318341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312545, d318341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d282284 q = 1) (hb : d312546 q = 1) : d318342 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d312546, d318342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312546, d318342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d282284 q = 1) (hb : d312547 q = 1) : d318343 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d312547, d318343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312547, d318343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83920 (p : Pattern) (ha : d282284 p = 1) (hb : d312553 p = 1) : d318349 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d282284 q = 1) (hb : d312548 q = 1) : d318344 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d312548, d318344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83919 q ha hb
    | true =>
      simp only [d312548, d318344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d282284 q = 1) (hb : d312549 q = 1) : d318345 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d312549, d318345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312549, d318345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d282284 q = 1) (hb : d312550 q = 1) : d318346 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d312550, d318346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312550, d318346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d282284 q = 1) (hb : d312551 q = 1) : d318347 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d312551, d318347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312551, d318347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d282284 q = 1) (hb : d312552 q = 1) : d318348 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d312552, d318348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312552, d318348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d282284 q = 1) (hb : d312553 q = 1) : d318349 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d312553, d318349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312553, d318349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83921 (p : Pattern) (ha : d282284 p = 1) (hb : d312559 p = 1) : d318355 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d282284 q = 1) (hb : d312554 q = 1) : d318350 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d312554, d318350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83916 q ha hb
    | true =>
      simp only [d312554, d318350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83920 q ha hb
  have h2 (q : Pattern) (ha : d282284 q = 1) (hb : d312555 q = 1) : d318351 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d312555, d318351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312555, d318351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d282284 q = 1) (hb : d312556 q = 1) : d318352 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d312556, d318352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312556, d318352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d282284 q = 1) (hb : d312557 q = 1) : d318353 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d312557, d318353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312557, d318353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d282284 q = 1) (hb : d312558 q = 1) : d318354 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d312558, d318354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312558, d318354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d282284 q = 1) (hb : d312559 q = 1) : d318355 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d312559, d318355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312559, d318355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83922 (p : Pattern) (ha : d282284 p = 1) (hb : d312565 p = 1) : d318361 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d35481 q = 1) (hb : d282284 q = 1) : d317143 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d35481, d317143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83651 q ha hb
    | true =>
      simp only [d35481, d317143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83654 q ha hb
  have h2 (q : Pattern) (ha : d35482 q = 1) (hb : d282284 q = 1) : d317144 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d35482, d317144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d35482, d317144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d282284 q = 1) (hb : d312514 q = 1) : d318315 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312514, d318315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d312514, d318315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d282284 q = 1) (hb : d312515 q = 1) : d318316 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312515, d318316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312515, d318316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d282284 q = 1) (hb : d312517 q = 1) : d318318 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312517, d318318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312517, d318318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83914 q ha hb
  have h6 (q : Pattern) (ha : d282284 q = 1) (hb : d312518 q = 1) : d318319 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312518, d318319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312518, d318319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d282284 q = 1) (hb : d312519 q = 1) : d318320 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312519, d318320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d312519, d318320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d282284 q = 1) (hb : d312520 q = 1) : d318321 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312520, d318321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d312520, d318321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d282284 q = 1) (hb : d312521 q = 1) : d318322 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312521, d318322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312521, d318322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d282284 q = 1) (hb : d312560 q = 1) : d318356 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d312560, d318356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312560, d318356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83921 q ha hb
  have h11 (q : Pattern) (ha : d282284 q = 1) (hb : d312561 q = 1) : d318357 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d312561, d318357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d312561, d318357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d282284 q = 1) (hb : d312562 q = 1) : d318358 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d312562, d318358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d312562, d318358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d282284 q = 1) (hb : d312563 q = 1) : d318359 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d312563, d318359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d312563, d318359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d282284 q = 1) (hb : d312564 q = 1) : d318360 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d312564, d318360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d312564, d318360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d282284 q = 1) (hb : d312565 q = 1) : d318361 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d312565, d318361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d312565, d318361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro83923 (p : Pattern) (ha : d282284 p = 1) (hb : d312571 p = 1) : d318367 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d282284 q = 1) (hb : d312566 q = 1) : d318362 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d312566, d318362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312566, d318362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83922 q ha hb
  have h2 (q : Pattern) (ha : d282284 q = 1) (hb : d312567 q = 1) : d318363 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d312567, d318363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312567, d318363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d282284 q = 1) (hb : d312568 q = 1) : d318364 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d312568, d318364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312568, d318364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d282284 q = 1) (hb : d312569 q = 1) : d318365 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d312569, d318365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312569, d318365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d282284 q = 1) (hb : d312570 q = 1) : d318366 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d312570, d318366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312570, d318366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d282284 q = 1) (hb : d312571 q = 1) : d318367 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d312571, d318367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d312571, d318367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83924 (p : Pattern) (ha : d282284 p = 1) (hb : d312577 p = 1) : d318373 p = 1 := by
  have h0 (q : Pattern) (ha : d282284 q = 1) (hb : d312426 q = 1) : d287276 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d312426, d287276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83897 q ha hb
    | true =>
      simp only [d312426, d287276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83901 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d282284 q = 1) (hb : d312453 q = 1) : d318254 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d312453, d318254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312453, d318254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83905 q ha hb
  have h3 (q : Pattern) (ha : d282284 q = 1) (hb : d312454 q = 1) : d318255 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d312454, d318255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d312454, d318255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d282284 q = 1) (hb : d312481 q = 1) : d318282 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d312481, d318282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312481, d318282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83909 q ha hb
  have h5 (q : Pattern) (ha : d282284 q = 1) (hb : d312482 q = 1) : d318283 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d312482, d318283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312482, d318283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d282284 q = 1) (hb : d312483 q = 1) : d318284 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d312483, d318284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312483, d318284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d282284 q = 1) (hb : d312510 q = 1) : d318311 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d312510, d318311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312510, d318311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83913 q ha hb
  have h8 (q : Pattern) (ha : d282284 q = 1) (hb : d312511 q = 1) : d318312 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d312511, d318312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312511, d318312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d282284 q = 1) (hb : d312512 q = 1) : d318313 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d312512, d318313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312512, d318313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d282284 q = 1) (hb : d312513 q = 1) : d318314 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d312513, d318314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d312513, d318314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d282284 q = 1) (hb : d312572 q = 1) : d318368 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d312572, d318368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312572, d318368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83923 q ha hb
  have h12 (q : Pattern) (ha : d282284 q = 1) (hb : d312573 q = 1) : d318369 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d312573, d318369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312573, d318369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d282284 q = 1) (hb : d312574 q = 1) : d318370 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d312574, d318370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312574, d318370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d282284 q = 1) (hb : d312575 q = 1) : d318371 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d312575, d318371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d312575, d318371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d282284 q = 1) (hb : d312576 q = 1) : d318372 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d312576, d318372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d312576, d318372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d282284 q = 1) (hb : d312577 q = 1) : d318373 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d312577, d318373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d312577, d318373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro83925 (p : Pattern) (ha : d282284 p = 1) (hb : d312583 p = 1) : d318379 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d282284 q = 1) (hb : d312578 q = 1) : d318374 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d312578, d318374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83924 q ha hb
    | true =>
      simp only [d312578, d318374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d282284 q = 1) (hb : d312579 q = 1) : d318375 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d312579, d318375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312579, d318375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d282284 q = 1) (hb : d312580 q = 1) : d318376 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d312580, d318376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312580, d318376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d282284 q = 1) (hb : d312581 q = 1) : d318377 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d312581, d318377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312581, d318377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d282284 q = 1) (hb : d312582 q = 1) : d318378 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d312582, d318378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312582, d318378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d282284 q = 1) (hb : d312583 q = 1) : d318379 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d312583, d318379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312583, d318379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83926 (p : Pattern) (ha : d282284 p = 1) (hb : d312589 p = 1) : d318385 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d282284 q = 1) (hb : d312584 q = 1) : d318380 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d312584, d318380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83925 q ha hb
    | true =>
      simp only [d312584, d318380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d282284 q = 1) (hb : d312585 q = 1) : d318381 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d312585, d318381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312585, d318381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d282284 q = 1) (hb : d312586 q = 1) : d318382 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d312586, d318382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312586, d318382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d282284 q = 1) (hb : d312587 q = 1) : d318383 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d312587, d318383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312587, d318383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d282284 q = 1) (hb : d312588 q = 1) : d318384 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d312588, d318384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312588, d318384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d282284 q = 1) (hb : d312589 q = 1) : d318385 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d312589, d318385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312589, d318385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83927 (p : Pattern) (ha : d282284 p = 1) (hb : d312595 p = 1) : d318391 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d282284 q = 1) (hb : d312590 q = 1) : d318386 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d312590, d318386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83926 q ha hb
    | true =>
      simp only [d312590, d318386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d282284 q = 1) (hb : d312591 q = 1) : d318387 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d312591, d318387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312591, d318387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d282284 q = 1) (hb : d312592 q = 1) : d318388 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d312592, d318388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312592, d318388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d282284 q = 1) (hb : d312593 q = 1) : d318389 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d312593, d318389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312593, d318389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d282284 q = 1) (hb : d312594 q = 1) : d318390 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d312594, d318390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312594, d318390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d282284 q = 1) (hb : d312595 q = 1) : d318391 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d312595, d318391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312595, d318391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83928 (p : Pattern) (ha : d282284 p = 1) (hb : d312601 p = 1) : d318397 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d282284 q = 1) (hb : d312596 q = 1) : d318392 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d312596, d318392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83927 q ha hb
    | true =>
      simp only [d312596, d318392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d282284 q = 1) (hb : d312597 q = 1) : d318393 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d312597, d318393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312597, d318393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d282284 q = 1) (hb : d312598 q = 1) : d318394 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d312598, d318394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312598, d318394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d282284 q = 1) (hb : d312599 q = 1) : d318395 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d312599, d318395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312599, d318395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d282284 q = 1) (hb : d312600 q = 1) : d318396 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d312600, d318396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312600, d318396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d282284 q = 1) (hb : d312601 q = 1) : d318397 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d312601, d318397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312601, d318397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83929 (p : Pattern) (ha : d282284 p = 1) (hb : d312607 p = 1) : d318403 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d282284 q = 1) (hb : d312602 q = 1) : d318398 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d312602, d318398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83928 q ha hb
    | true =>
      simp only [d312602, d318398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d282284 q = 1) (hb : d312603 q = 1) : d318399 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d312603, d318399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312603, d318399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d282284 q = 1) (hb : d312604 q = 1) : d318400 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d312604, d318400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312604, d318400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d282284 q = 1) (hb : d312605 q = 1) : d318401 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d312605, d318401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312605, d318401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d282284 q = 1) (hb : d312606 q = 1) : d318402 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d312606, d318402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312606, d318402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d282284 q = 1) (hb : d312607 q = 1) : d318403 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d312607, d318403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312607, d318403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83930 (p : Pattern) (ha : d282284 p = 1) (hb : d312613 p = 1) : d318409 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d282284 q = 1) (hb : d312608 q = 1) : d318404 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d312608, d318404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83929 q ha hb
    | true =>
      simp only [d312608, d318404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d282284 q = 1) (hb : d312609 q = 1) : d318405 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d312609, d318405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312609, d318405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d282284 q = 1) (hb : d312610 q = 1) : d318406 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d312610, d318406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312610, d318406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d282284 q = 1) (hb : d312611 q = 1) : d318407 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d312611, d318407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312611, d318407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d282284 q = 1) (hb : d312612 q = 1) : d318408 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d312612, d318408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312612, d318408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d282284 q = 1) (hb : d312613 q = 1) : d318409 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d312613, d318409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312613, d318409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83931 (p : Pattern) (ha : d282284 p = 1) (hb : d312619 p = 1) : d318415 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282284 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d282284 q = 1) (hb : d312614 q = 1) : d318410 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d312614, d318410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83930 q ha hb
    | true =>
      simp only [d312614, d318410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d282284 q = 1) (hb : d312615 q = 1) : d318411 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d312615, d318411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d312615, d318411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d282284 q = 1) (hb : d312616 q = 1) : d318412 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d312616, d318412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d312616, d318412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d282284 q = 1) (hb : d312617 q = 1) : d318413 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d312617, d318413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d312617, d318413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d282284 q = 1) (hb : d312618 q = 1) : d318414 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d312618, d318414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312618, d318414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d282284 q = 1) (hb : d312619 q = 1) : d318415 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d312619, d318415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d312619, d318415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83932 (p : Pattern) (ha : d315316 p = 1) (hb : d316540 p = 1) : d317482 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d315267 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d315276 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d315296 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d315241 q = 1) (hb : d316535 q = 1) : d317477 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315241, d316535, d317477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83724 q ha hb
    | true =>
      simp only [d315241, d316535, d317477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83725 q ha hb
  have h5 (q : Pattern) (ha : d315297 q = 1) (hb : d316536 q = 1) : d317478 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315297, d316536, d317478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d315297, d316536, d317478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d315312 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d315313 q = 1) (hb : d316537 q = 1) : d317479 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315313, d316537, d317479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315313, d316537, d317479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d315314 q = 1) (hb : d316538 q = 1) : d317480 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315314, d316538, d317480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d315314, d316538, d317480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d315315 q = 1) (hb : d316539 q = 1) : d317481 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d315315, d316539, d317481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d315315, d316539, d317481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d315316 q = 1) (hb : d316540 q = 1) : d317482 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d315316, d316540, d317482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315316, d316540, d317482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro83933 (p : Pattern) (ha : d315337 p = 1) (hb : d316550 p = 1) : d317492 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d315267 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d315276 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d315296 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d315241 q = 1) (hb : d316535 q = 1) : d317477 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315241, d316535, d317477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83724 q ha hb
    | true =>
      simp only [d315241, d316535, d317477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83725 q ha hb
  have h4 (q : Pattern) (ha : d315297 q = 1) (hb : d316536 q = 1) : d317478 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315297, d316536, d317478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d315297, d316536, d317478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d315312 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d315313 q = 1) (hb : d316537 q = 1) : d317479 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315313, d316537, d317479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315313, d316537, d317479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d315314 q = 1) (hb : d316538 q = 1) : d317480 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315314, d316538, d317480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d315314, d316538, d317480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d315315 q = 1) (hb : d316539 q = 1) : d317481 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d315315, d316539, d317481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315315, d316539, d317481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d315322 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d315327 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d315329 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d315251 q = 1) (hb : d316545 q = 1) : d317487 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315251, d316545, d317487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83727 q ha hb
    | true =>
      simp only [d315251, d316545, d317487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83728 q ha hb
  have h13 (q : Pattern) (ha : d315330 q = 1) (hb : d316546 q = 1) : d317488 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315330, d316546, d317488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d315330, d316546, d317488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d315333 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d315334 q = 1) (hb : d316547 q = 1) : d317489 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315334, d316547, d317489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d315334, d316547, d317489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d315335 q = 1) (hb : d316548 q = 1) : d317490 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315335, d316548, d317490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d315335, d316548, d317490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d315336 q = 1) (hb : d316549 q = 1) : d317491 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d315336, d316549, d317491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d315336, d316549, d317491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d315337 q = 1) (hb : d316550 q = 1) : d317492 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d315337, d316550, d317492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d315337, d316550, d317492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro83934 (p : Pattern) (ha : d315357 p = 1) (hb : d318258 p = 1) : d318418 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d315329 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d315251 q = 1) (hb : d316545 q = 1) : d317487 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315251, d316545, d317487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83727 q ha hb
    | true =>
      simp only [d315251, d316545, d317487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83728 q ha hb
  have h3 (q : Pattern) (ha : d315330 q = 1) (hb : d316546 q = 1) : d317488 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315330, d316546, d317488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d315330, d316546, d317488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d315333 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d315334 q = 1) (hb : d316547 q = 1) : d317489 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315334, d316547, d317489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315334, d316547, d317489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d315355 q = 1) (hb : d316548 q = 1) : d317490 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315355, d316548, d317490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315355, d316548, d317490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d315356 q = 1) (hb : d316549 q = 1) : d317491 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d315356, d316549, d317491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315356, d316549, d317491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d315357 q = 1) (hb : d318258 q = 1) : d318418 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d315357, d318258, d318418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315357, d318258, d318418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83935 (p : Pattern) (ha : d315466 p = 1) (hb : d318269 p = 1) : d318429 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d315441 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d315446 q = 1) (hb : d318264 q = 1) : d318424 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315446, d318264, d318424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83760 q ha hb
    | true =>
      simp only [d315446, d318264, d318424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83765 q ha hb
  have h3 (q : Pattern) (ha : d315447 q = 1) (hb : d318265 q = 1) : d318425 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315447, d318265, d318425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d315447, d318265, d318425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d315462 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d315463 q = 1) (hb : d318266 q = 1) : d318426 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315463, d318266, d318426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315463, d318266, d318426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d315464 q = 1) (hb : d318267 q = 1) : d318427 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315464, d318267, d318427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315464, d318267, d318427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d315465 q = 1) (hb : d318268 q = 1) : d318428 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d315465, d318268, d318428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315465, d318268, d318428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d315466 q = 1) (hb : d318269 q = 1) : d318429 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d315466, d318269, d318429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315466, d318269, d318429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83936 (p : Pattern) (ha : d315479 p = 1) (hb : d318275 p = 1) : d318435 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d315259 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315338 q = 1) (hb : d316551 q = 1) : d317493 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d315338, d316551, d317493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83932 q ha hb
    | true =>
      simp only [d315338, d316551, d317493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83933 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d315351 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d315352 q = 1) (hb : d316552 q = 1) : d317494 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d315352, d316552, d317494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d315352, d316552, d317494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d315353 q = 1) (hb : d318256 q = 1) : d318416 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d315353, d318256, d318416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315353, d318256, d318416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d315354 q = 1) (hb : d318257 q = 1) : d318417 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d315354, d318257, d318417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315354, d318257, d318417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d315358 q = 1) (hb : d318259 q = 1) : d318419 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d315358, d318259, d318419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d315358, d318259, d318419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83934 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d315360 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d315361 q = 1) (hb : d318260 q = 1) : d318420 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d315361, d318260, d318420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d315361, d318260, d318420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d315362 q = 1) (hb : d318261 q = 1) : d318421 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d315362, d318261, d318421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d315362, d318261, d318421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d315363 q = 1) (hb : d318262 q = 1) : d318422 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d315363, d318262, d318422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d315363, d318262, d318422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d315364 q = 1) (hb : d318263 q = 1) : d318423 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d315364, d318263, d318423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315364, d318263, d318423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d315467 q = 1) (hb : d318270 q = 1) : d318430 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d315467, d318270, d318430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d315467, d318270, d318430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83935 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d315474 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d315475 q = 1) (hb : d318271 q = 1) : d318431 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d315475, d318271, d318431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d315475, d318271, d318431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d315476 q = 1) (hb : d318272 q = 1) : d318432 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d315476, d318272, d318432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d315476, d318272, d318432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d315477 q = 1) (hb : d318273 q = 1) : d318433 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d315477, d318273, d318433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d315477, d318273, d318433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d315478 q = 1) (hb : d318274 q = 1) : d318434 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d315478, d318274, d318434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d315478, d318274, d318434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d315479 q = 1) (hb : d318275 q = 1) : d318435 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d315479, d318275, d318435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d315479, d318275, d318435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro83937 (p : Pattern) (ha : d315485 p = 1) (hb : d318281 p = 1) : d318441 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315480 q = 1) (hb : d318276 q = 1) : d318436 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d315480, d318276, d318436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315480, d318276, d318436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83936 q ha hb
  have h2 (q : Pattern) (ha : d315481 q = 1) (hb : d318277 q = 1) : d318437 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d315481, d318277, d318437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315481, d318277, d318437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315482 q = 1) (hb : d318278 q = 1) : d318438 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d315482, d318278, d318438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315482, d318278, d318438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315483 q = 1) (hb : d318279 q = 1) : d318439 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d315483, d318279, d318439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315483, d318279, d318439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315484 q = 1) (hb : d318280 q = 1) : d318440 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d315484, d318280, d318440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315484, d318280, d318440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315485 q = 1) (hb : d318281 q = 1) : d318441 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d315485, d318281, d318441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315485, d318281, d318441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83938 (p : Pattern) (ha : d315664 p = 1) (hb : d316827 p = 1) : d317766 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d315599 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d315608 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d315628 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d315573 q = 1) (hb : d316822 q = 1) : d317761 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315573, d316822, d317761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83782 q ha hb
    | true =>
      simp only [d315573, d316822, d317761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83783 q ha hb
  have h5 (q : Pattern) (ha : d315629 q = 1) (hb : d316823 q = 1) : d317762 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315629, d316823, d317762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d315629, d316823, d317762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d315660 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d315661 q = 1) (hb : d316824 q = 1) : d317763 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315661, d316824, d317763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315661, d316824, d317763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d315662 q = 1) (hb : d316825 q = 1) : d317764 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315662, d316825, d317764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d315662, d316825, d317764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d315663 q = 1) (hb : d316826 q = 1) : d317765 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d315663, d316826, d317765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d315663, d316826, d317765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d315664 q = 1) (hb : d316827 q = 1) : d317766 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d315664, d316827, d317766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315664, d316827, d317766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro83939 (p : Pattern) (ha : d315685 p = 1) (hb : d316837 p = 1) : d317776 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d315599 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d315608 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d315628 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d315573 q = 1) (hb : d316822 q = 1) : d317761 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315573, d316822, d317761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83782 q ha hb
    | true =>
      simp only [d315573, d316822, d317761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83783 q ha hb
  have h4 (q : Pattern) (ha : d315629 q = 1) (hb : d316823 q = 1) : d317762 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315629, d316823, d317762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d315629, d316823, d317762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d315660 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d315661 q = 1) (hb : d316824 q = 1) : d317763 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315661, d316824, d317763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315661, d316824, d317763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d315662 q = 1) (hb : d316825 q = 1) : d317764 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315662, d316825, d317764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d315662, d316825, d317764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d315663 q = 1) (hb : d316826 q = 1) : d317765 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d315663, d316826, d317765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315663, d316826, d317765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d315670 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d315675 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d315677 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d315583 q = 1) (hb : d316832 q = 1) : d317771 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315583, d316832, d317771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83785 q ha hb
    | true =>
      simp only [d315583, d316832, d317771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83786 q ha hb
  have h13 (q : Pattern) (ha : d315678 q = 1) (hb : d316833 q = 1) : d317772 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315678, d316833, d317772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d315678, d316833, d317772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d315681 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d315682 q = 1) (hb : d316834 q = 1) : d317773 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315682, d316834, d317773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d315682, d316834, d317773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d315683 q = 1) (hb : d316835 q = 1) : d317774 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315683, d316835, d317774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d315683, d316835, d317774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d315684 q = 1) (hb : d316836 q = 1) : d317775 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d315684, d316836, d317775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d315684, d316836, d317775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d315685 q = 1) (hb : d316837 q = 1) : d317776 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d315685, d316837, d317776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d315685, d316837, d317776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro83940 (p : Pattern) (ha : d315705 p = 1) (hb : d318287 p = 1) : d318447 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d315677 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d315583 q = 1) (hb : d316832 q = 1) : d317771 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315583, d316832, d317771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83785 q ha hb
    | true =>
      simp only [d315583, d316832, d317771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83786 q ha hb
  have h3 (q : Pattern) (ha : d315678 q = 1) (hb : d316833 q = 1) : d317772 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315678, d316833, d317772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d315678, d316833, d317772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d315681 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d315682 q = 1) (hb : d316834 q = 1) : d317773 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315682, d316834, d317773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315682, d316834, d317773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d315703 q = 1) (hb : d316835 q = 1) : d317774 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315703, d316835, d317774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315703, d316835, d317774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d315704 q = 1) (hb : d316836 q = 1) : d317775 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d315704, d316836, d317775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315704, d316836, d317775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d315705 q = 1) (hb : d318287 q = 1) : d318447 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d315705, d318287, d318447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315705, d318287, d318447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83941 (p : Pattern) (ha : d315825 p = 1) (hb : d318298 p = 1) : d318458 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d315789 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d315794 q = 1) (hb : d318293 q = 1) : d318453 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315794, d318293, d318453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83821 q ha hb
    | true =>
      simp only [d315794, d318293, d318453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83827 q ha hb
  have h3 (q : Pattern) (ha : d315795 q = 1) (hb : d318294 q = 1) : d318454 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315795, d318294, d318454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d315795, d318294, d318454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d315821 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d315822 q = 1) (hb : d318295 q = 1) : d318455 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d315822, d318295, d318455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315822, d318295, d318455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d315823 q = 1) (hb : d318296 q = 1) : d318456 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d315823, d318296, d318456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315823, d318296, d318456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d315824 q = 1) (hb : d318297 q = 1) : d318457 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d315824, d318297, d318457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315824, d318297, d318457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d315825 q = 1) (hb : d318298 q = 1) : d318458 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d315825, d318298, d318458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315825, d318298, d318458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83942 (p : Pattern) (ha : d315838 p = 1) (hb : d318304 p = 1) : d318464 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d315591 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315686 q = 1) (hb : d316838 q = 1) : d317777 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d315686, d316838, d317777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83938 q ha hb
    | true =>
      simp only [d315686, d316838, d317777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83939 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d315699 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d315700 q = 1) (hb : d316839 q = 1) : d317778 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d315700, d316839, d317778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d315700, d316839, d317778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d315701 q = 1) (hb : d318285 q = 1) : d318445 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d315701, d318285, d318445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315701, d318285, d318445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d315702 q = 1) (hb : d318286 q = 1) : d318446 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d315702, d318286, d318446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315702, d318286, d318446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d315706 q = 1) (hb : d318288 q = 1) : d318448 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d315706, d318288, d318448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d315706, d318288, d318448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83940 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d315708 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d315709 q = 1) (hb : d318289 q = 1) : d318449 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d315709, d318289, d318449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d315709, d318289, d318449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d315710 q = 1) (hb : d318290 q = 1) : d318450 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d315710, d318290, d318450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d315710, d318290, d318450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d315711 q = 1) (hb : d318291 q = 1) : d318451 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d315711, d318291, d318451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d315711, d318291, d318451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d315712 q = 1) (hb : d318292 q = 1) : d318452 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d315712, d318292, d318452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315712, d318292, d318452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d315826 q = 1) (hb : d318299 q = 1) : d318459 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d315826, d318299, d318459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d315826, d318299, d318459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83941 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d315833 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d315834 q = 1) (hb : d318300 q = 1) : d318460 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d315834, d318300, d318460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d315834, d318300, d318460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d315835 q = 1) (hb : d318301 q = 1) : d318461 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d315835, d318301, d318461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d315835, d318301, d318461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d315836 q = 1) (hb : d318302 q = 1) : d318462 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d315836, d318302, d318462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d315836, d318302, d318462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d315837 q = 1) (hb : d318303 q = 1) : d318463 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d315837, d318303, d318463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d315837, d318303, d318463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d315838 q = 1) (hb : d318304 q = 1) : d318464 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d315838, d318304, d318464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d315838, d318304, d318464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro83943 (p : Pattern) (ha : d315844 p = 1) (hb : d318310 p = 1) : d318470 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d315839 q = 1) (hb : d318305 q = 1) : d318465 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d315839, d318305, d318465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315839, d318305, d318465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83942 q ha hb
  have h2 (q : Pattern) (ha : d315840 q = 1) (hb : d318306 q = 1) : d318466 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d315840, d318306, d318466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315840, d318306, d318466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d315841 q = 1) (hb : d318307 q = 1) : d318467 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d315841, d318307, d318467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315841, d318307, d318467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315842 q = 1) (hb : d318308 q = 1) : d318468 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d315842, d318308, d318468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315842, d318308, d318468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315843 q = 1) (hb : d318309 q = 1) : d318469 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d315843, d318309, d318469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315843, d318309, d318469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d315844 q = 1) (hb : d318310 q = 1) : d318470 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d315844, d318310, d318470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315844, d318310, d318470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83944 (p : Pattern) (ha : d316008 p = 1) (hb : d317132 p = 1) : d318012 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d315945 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d315954 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d315972 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d315919 q = 1) (hb : d317127 q = 1) : d318007 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315919, d317127, d318007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83838 q ha hb
    | true =>
      simp only [d315919, d317127, d318007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83839 q ha hb
  have h5 (q : Pattern) (ha : d315973 q = 1) (hb : d317128 q = 1) : d318008 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315973, d317128, d318008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d315973, d317128, d318008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d316004 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d316005 q = 1) (hb : d317129 q = 1) : d318009 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d316005, d317129, d318009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316005, d317129, d318009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d316006 q = 1) (hb : d317130 q = 1) : d318010 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d316006, d317130, d318010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d316006, d317130, d318010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d316007 q = 1) (hb : d317131 q = 1) : d318011 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d316007, d317131, d318011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d316007, d317131, d318011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d316008 q = 1) (hb : d317132 q = 1) : d318012 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d316008, d317132, d318012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316008, d317132, d318012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro83945 (p : Pattern) (ha : d316029 p = 1) (hb : d317142 p = 1) : d318022 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d315945 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d315954 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d315972 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d315919 q = 1) (hb : d317127 q = 1) : d318007 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315919, d317127, d318007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83838 q ha hb
    | true =>
      simp only [d315919, d317127, d318007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83839 q ha hb
  have h4 (q : Pattern) (ha : d315973 q = 1) (hb : d317128 q = 1) : d318008 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d315973, d317128, d318008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d315973, d317128, d318008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d316004 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d316005 q = 1) (hb : d317129 q = 1) : d318009 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d316005, d317129, d318009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d316005, d317129, d318009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d316006 q = 1) (hb : d317130 q = 1) : d318010 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d316006, d317130, d318010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d316006, d317130, d318010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d316007 q = 1) (hb : d317131 q = 1) : d318011 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d316007, d317131, d318011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316007, d317131, d318011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d316014 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d316019 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d316021 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d315929 q = 1) (hb : d317137 q = 1) : d318017 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315929, d317137, d318017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83841 q ha hb
    | true =>
      simp only [d315929, d317137, d318017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83842 q ha hb
  have h13 (q : Pattern) (ha : d316022 q = 1) (hb : d317138 q = 1) : d318018 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d316022, d317138, d318018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d316022, d317138, d318018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d316025 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d316026 q = 1) (hb : d317139 q = 1) : d318019 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d316026, d317139, d318019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d316026, d317139, d318019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d316027 q = 1) (hb : d317140 q = 1) : d318020 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d316027, d317140, d318020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d316027, d317140, d318020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d316028 q = 1) (hb : d317141 q = 1) : d318021 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d316028, d317141, d318021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d316028, d317141, d318021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d316029 q = 1) (hb : d317142 q = 1) : d318022 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d316029, d317142, d318022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d316029, d317142, d318022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro83946 (p : Pattern) (ha : d316049 p = 1) (hb : d318317 p = 1) : d318477 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d316021 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d315929 q = 1) (hb : d317137 q = 1) : d318017 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d315929, d317137, d318017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83841 q ha hb
    | true =>
      simp only [d315929, d317137, d318017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83842 q ha hb
  have h3 (q : Pattern) (ha : d316022 q = 1) (hb : d317138 q = 1) : d318018 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d316022, d317138, d318018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d316022, d317138, d318018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d316025 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d316026 q = 1) (hb : d317139 q = 1) : d318019 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d316026, d317139, d318019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d316026, d317139, d318019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d316047 q = 1) (hb : d317140 q = 1) : d318020 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d316047, d317140, d318020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316047, d317140, d318020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d316048 q = 1) (hb : d317141 q = 1) : d318021 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d316048, d317141, d318021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316048, d317141, d318021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d316049 q = 1) (hb : d318317 q = 1) : d318477 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d316049, d318317, d318477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316049, d318317, d318477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83947 (p : Pattern) (ha : d316108 p = 1) (hb : d317323 p = 1) : d318130 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316068 q = 1) (hb : d317262 q = 1) : d317262 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d316088 q = 1) (hb : d317280 q = 1) : d318117 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d316088, d317280, d318117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d316088, d317280, d318117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83870 q ha hb
  have h3 (q : Pattern) (ha : d316089 q = 1) (hb : d317281 q = 1) : d318118 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d316089, d317281, d318118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316089, d317281, d318118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d316090 q = 1) (hb : d317282 q = 1) : d318119 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d316090, d317282, d318119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316090, d317282, d318119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d316097 q = 1) (hb : d317288 q = 1) : d317288 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d316098 q = 1) (hb : d317289 q = 1) : d318120 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d316098, d317289, d318120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83870 q ha hb
    | true =>
      simp only [d316098, d317289, d318120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d316099 q = 1) (hb : d317290 q = 1) : d318121 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d316099, d317290, d318121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316099, d317290, d318121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d316100 q = 1) (hb : d317291 q = 1) : d318122 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d316100, d317291, d318122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316100, d317291, d318122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d316101 q = 1) (hb : d317292 q = 1) : d318123 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d316101, d317292, d318123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d316101, d317292, d318123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d316098 q = 1) (hb : d317308 q = 1) : d318120 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d316098, d317308, d318120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83870 q ha hb
    | true =>
      simp only [d316098, d317308, d318120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83874 q ha hb
  have h11 (q : Pattern) (ha : d316099 q = 1) (hb : d317309 q = 1) : d318121 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d316099, d317309, d318121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316099, d317309, d318121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d316100 q = 1) (hb : d317310 q = 1) : d318122 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d316100, d317310, d318122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316100, d317310, d318122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d316106 q = 1) (hb : d317311 q = 1) : d318128 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d316106, d317311, d318128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d316106, d317311, d318128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d316107 q = 1) (hb : d317322 q = 1) : d318129 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d316107, d317322, d318129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d316107, d317322, d318129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d316108 q = 1) (hb : d317323 q = 1) : d318130 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d316108, d317323, d318130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d316108, d317323, d318130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h15 p ha hb
theorem andIntro83948 (p : Pattern) (ha : d316122 p = 1) (hb : d318326 p = 1) : d318144 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316109 q = 1) (hb : d317324 q = 1) : d318131 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d316109, d317324, d318131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83947 q ha hb
    | true =>
      simp only [d316109, d317324, d318131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d316110 q = 1) (hb : d317325 q = 1) : d318132 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d316110, d317325, d318132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316110, d317325, d318132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d316117 q = 1) (hb : d317314 q = 1) : d318139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d316117, d317314, d318139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83875 q ha hb
    | true =>
      simp only [d316117, d317314, d318139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d316118 q = 1) (hb : d317315 q = 1) : d318140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d316118, d317315, d318140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316118, d317315, d318140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d316119 q = 1) (hb : d318323 q = 1) : d318141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d316119, d318323, d318141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d316119, d318323, d318141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d316120 q = 1) (hb : d318324 q = 1) : d318142 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d316120, d318324, d318142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316120, d318324, d318142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d316121 q = 1) (hb : d318325 q = 1) : d318143 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d316121, d318325, d318143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d316121, d318325, d318143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d316122 q = 1) (hb : d318326 q = 1) : d318144 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d316122, d318326, d318144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d316122, d318326, d318144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro83949 (p : Pattern) (ha : d53301 p = 1) (hb : d258695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53301 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44880 q = 1) (hb : d51979 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d44880, d51979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44880, d51979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d53295 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d46864, d53295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46864, d53295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d46865 q = 1) (hb : d53300 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d46865, d53300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46865, d53300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d46866 q = 1) (hb : d53301 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d46866, d53301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46866, d53301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d53301 q = 1) (hb : d258695 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d258695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d258695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro83950 (p : Pattern) (ha : d315891 p = 1) (hb : d318331 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53297 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53301 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53301 q = 1) (hb : d258696 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d258696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83949 q ha hb
    | true =>
      simp only [d258696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d315859 q = 1) (hb : d318327 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d315859, d318327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d315859, d318327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d315860 q = 1) (hb : d318328 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315860, d318328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315860, d318328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d315861 q = 1) (hb : d318329 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d315861, d318329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315861, d318329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h7 (q : Pattern) (ha : d315862 q = 1) (hb : d318330 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d315862, d318330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315862, d318330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h8 (q : Pattern) (ha : d315891 q = 1) (hb : d318331 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d315891, d318331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d315891, d318331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  exact h8 p ha hb
theorem andIntro83951 (p : Pattern) (ha : d316097 p = 1) (hb : d318337 p = 1) : d317288 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316082 q = 1) (hb : d317274 q = 1) : d317283 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d316082, d317274, d317283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316082, d317274, d317283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83833 q ha hb
  have h2 (q : Pattern) (ha : d315880 q = 1) (hb : d317085 q = 1) : d317095 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315880, d317085, d317095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83833 q ha hb
    | true =>
      simp only [d315880, d317085, d317095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d316083 q = 1) (hb : d317275 q = 1) : d317284 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d316083, d317275, d317284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d316083, d317275, d317284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315881 q = 1) (hb : d317086 q = 1) : d317096 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315881, d317086, d317096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d315881, d317086, d317096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d316084 q = 1) (hb : d317276 q = 1) : d317285 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d316084, d317276, d317285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d316084, d317276, d317285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d316085 q = 1) (hb : d317277 q = 1) : d317286 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d316085, d317277, d317286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316085, d317277, d317286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d316091 q = 1) (hb : d317306 q = 1) : d317287 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d316091, d317306, d317287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d316091, d317306, d317287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d316093 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d315892 q = 1) (hb : d318332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d315892, d318332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83950 q ha hb
    | true =>
      simp only [d315892, d318332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d315893 q = 1) (hb : d318333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d315893, d318333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d315893, d318333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d316094 q = 1) (hb : d318334 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d316094, d318334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d316094, d318334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d316095 q = 1) (hb : d318335 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d316095, d318335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d316095, d318335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d316096 q = 1) (hb : d318336 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d316096, d318336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d316096, d318336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d316097 q = 1) (hb : d318337 q = 1) : d317288 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d316097, d318337, d317288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d316097, d318337, d317288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro83952 (p : Pattern) (ha : d316116 p = 1) (hb : d318343 p = 1) : d318138 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316098 q = 1) (hb : d318338 q = 1) : d318120 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d316098, d318338, d318120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83870 q ha hb
    | true =>
      simp only [d316098, d318338, d318120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83951 q ha hb
  have h2 (q : Pattern) (ha : d316099 q = 1) (hb : d318339 q = 1) : d318121 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d316099, d318339, d318121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316099, d318339, d318121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d316100 q = 1) (hb : d318340 q = 1) : d318122 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d316100, d318340, d318122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316100, d318340, d318122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d316106 q = 1) (hb : d318341 q = 1) : d318128 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d316106, d318341, d318128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d316106, d318341, d318128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d316115 q = 1) (hb : d318342 q = 1) : d318137 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d316115, d318342, d318137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d316115, d318342, d318137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d316116 q = 1) (hb : d318343 q = 1) : d318138 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d316116, d318343, d318138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316116, d318343, d318138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83953 (p : Pattern) (ha : d316127 p = 1) (hb : d318349 p = 1) : d318161 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316117 q = 1) (hb : d318344 q = 1) : d318139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d316117, d318344, d318139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83952 q ha hb
    | true =>
      simp only [d316117, d318344, d318139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d316118 q = 1) (hb : d318345 q = 1) : d318140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d316118, d318345, d318140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316118, d318345, d318140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d316124 q = 1) (hb : d318346 q = 1) : d318158 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d316124, d318346, d318158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d316124, d318346, d318158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d316125 q = 1) (hb : d318347 q = 1) : d318159 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d316125, d318347, d318159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d316125, d318347, d318159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d316126 q = 1) (hb : d318348 q = 1) : d318160 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d316126, d318348, d318160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d316126, d318348, d318160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d316127 q = 1) (hb : d318349 q = 1) : d318161 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d316127, d318349, d318161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316127, d318349, d318161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83954 (p : Pattern) (ha : d316159 p = 1) (hb : d318355 p = 1) : d318488 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d316123 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d316128 q = 1) (hb : d318350 q = 1) : d318483 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d316128, d318350, d318483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83948 q ha hb
    | true =>
      simp only [d316128, d318350, d318483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83953 q ha hb
  have h3 (q : Pattern) (ha : d316129 q = 1) (hb : d318351 q = 1) : d318484 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d316129, d318351, d318484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d316129, d318351, d318484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d316155 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d316156 q = 1) (hb : d318352 q = 1) : d318485 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d316156, d318352, d318485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d316156, d318352, d318485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d316157 q = 1) (hb : d318353 q = 1) : d318486 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d316157, d318353, d318486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316157, d318353, d318486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d316158 q = 1) (hb : d318354 q = 1) : d318487 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d316158, d318354, d318487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316158, d318354, d318487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d316159 q = 1) (hb : d318355 q = 1) : d318488 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d316159, d318355, d318488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316159, d318355, d318488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83955 (p : Pattern) (ha : d316172 p = 1) (hb : d318361 p = 1) : d318494 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d315937 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316030 q = 1) (hb : d317143 q = 1) : d318023 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d316030, d317143, d318023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83944 q ha hb
    | true =>
      simp only [d316030, d317143, d318023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83945 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d316043 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d316044 q = 1) (hb : d317144 q = 1) : d318024 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d316044, d317144, d318024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d316044, d317144, d318024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d316045 q = 1) (hb : d318315 q = 1) : d318475 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d316045, d318315, d318475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d316045, d318315, d318475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d316046 q = 1) (hb : d318316 q = 1) : d318476 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d316046, d318316, d318476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316046, d318316, d318476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d316050 q = 1) (hb : d318318 q = 1) : d318478 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d316050, d318318, d318478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d316050, d318318, d318478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83946 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d316052 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d316053 q = 1) (hb : d318319 q = 1) : d318479 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d316053, d318319, d318479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d316053, d318319, d318479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d316054 q = 1) (hb : d318320 q = 1) : d318480 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d316054, d318320, d318480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d316054, d318320, d318480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d316055 q = 1) (hb : d318321 q = 1) : d318481 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d316055, d318321, d318481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d316055, d318321, d318481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d316056 q = 1) (hb : d318322 q = 1) : d318482 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d316056, d318322, d318482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d316056, d318322, d318482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d316160 q = 1) (hb : d318356 q = 1) : d318489 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d316160, d318356, d318489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d316160, d318356, d318489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83954 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d316167 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d316168 q = 1) (hb : d318357 q = 1) : d318490 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d316168, d318357, d318490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d316168, d318357, d318490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d316169 q = 1) (hb : d318358 q = 1) : d318491 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d316169, d318358, d318491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d316169, d318358, d318491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d316170 q = 1) (hb : d318359 q = 1) : d318492 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d316170, d318359, d318492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d316170, d318359, d318492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d316171 q = 1) (hb : d318360 q = 1) : d318493 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d316171, d318360, d318493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d316171, d318360, d318493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d316172 q = 1) (hb : d318361 q = 1) : d318494 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d316172, d318361, d318494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d316172, d318361, d318494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro83956 (p : Pattern) (ha : d316178 p = 1) (hb : d318367 p = 1) : d318500 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316173 q = 1) (hb : d318362 q = 1) : d318495 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d316173, d318362, d318495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316173, d318362, d318495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83955 q ha hb
  have h2 (q : Pattern) (ha : d316174 q = 1) (hb : d318363 q = 1) : d318496 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d316174, d318363, d318496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316174, d318363, d318496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d316175 q = 1) (hb : d318364 q = 1) : d318497 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d316175, d318364, d318497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316175, d318364, d318497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d316176 q = 1) (hb : d318365 q = 1) : d318498 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d316176, d318365, d318498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316176, d318365, d318498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d316177 q = 1) (hb : d318366 q = 1) : d318499 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d316177, d318366, d318499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316177, d318366, d318499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d316178 q = 1) (hb : d318367 q = 1) : d318500 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d316178, d318367, d318500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d316178, d318367, d318500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83957 (p : Pattern) (ha : d316184 p = 1) (hb : d318373 p = 1) : d318506 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d318255 q = 1) : d318255 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d315486 q = 1) (hb : d318282 q = 1) : d318442 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d315486, d318282, d318442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d315486, d318282, d318442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83937 q ha hb
  have h3 (q : Pattern) (ha : d315487 q = 1) (hb : d318283 q = 1) : d318443 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d315487, d318283, d318443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d315487, d318283, d318443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d315488 q = 1) (hb : d318284 q = 1) : d318444 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d315488, d318284, d318444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d315488, d318284, d318444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d315845 q = 1) (hb : d318311 q = 1) : d318471 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d315845, d318311, d318471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d315845, d318311, d318471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83943 q ha hb
  have h6 (q : Pattern) (ha : d315846 q = 1) (hb : d318312 q = 1) : d318472 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d315846, d318312, d318472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d315846, d318312, d318472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d315847 q = 1) (hb : d318313 q = 1) : d318473 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d315847, d318313, d318473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d315847, d318313, d318473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d315848 q = 1) (hb : d318314 q = 1) : d318474 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d315848, d318314, d318474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d315848, d318314, d318474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d316179 q = 1) (hb : d318368 q = 1) : d318501 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d316179, d318368, d318501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d316179, d318368, d318501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83956 q ha hb
  have h10 (q : Pattern) (ha : d316180 q = 1) (hb : d318369 q = 1) : d318502 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d316180, d318369, d318502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d316180, d318369, d318502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d316181 q = 1) (hb : d318370 q = 1) : d318503 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d316181, d318370, d318503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d316181, d318370, d318503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d316182 q = 1) (hb : d318371 q = 1) : d318504 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d316182, d318371, d318504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d316182, d318371, d318504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d316183 q = 1) (hb : d318372 q = 1) : d318505 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d316183, d318372, d318505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d316183, d318372, d318505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d316184 q = 1) (hb : d318373 q = 1) : d318506 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d316184, d318373, d318506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d316184, d318373, d318506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h14 p ha hb
theorem andIntro83958 (p : Pattern) (ha : d316190 p = 1) (hb : d318379 p = 1) : d318512 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316185 q = 1) (hb : d318374 q = 1) : d318507 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d316185, d318374, d318507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83957 q ha hb
    | true =>
      simp only [d316185, d318374, d318507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d316186 q = 1) (hb : d318375 q = 1) : d318508 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d316186, d318375, d318508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d316186, d318375, d318508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d316187 q = 1) (hb : d318376 q = 1) : d318509 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d316187, d318376, d318509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d316187, d318376, d318509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d316188 q = 1) (hb : d318377 q = 1) : d318510 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d316188, d318377, d318510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d316188, d318377, d318510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d316189 q = 1) (hb : d318378 q = 1) : d318511 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d316189, d318378, d318511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d316189, d318378, d318511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d316190 q = 1) (hb : d318379 q = 1) : d318512 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d316190, d318379, d318512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316190, d318379, d318512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83959 (p : Pattern) (ha : d316196 p = 1) (hb : d318385 p = 1) : d318518 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316191 q = 1) (hb : d318380 q = 1) : d318513 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d316191, d318380, d318513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83958 q ha hb
    | true =>
      simp only [d316191, d318380, d318513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d316192 q = 1) (hb : d318381 q = 1) : d318514 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d316192, d318381, d318514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d316192, d318381, d318514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d316193 q = 1) (hb : d318382 q = 1) : d318515 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d316193, d318382, d318515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d316193, d318382, d318515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d316194 q = 1) (hb : d318383 q = 1) : d318516 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d316194, d318383, d318516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d316194, d318383, d318516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d316195 q = 1) (hb : d318384 q = 1) : d318517 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d316195, d318384, d318517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d316195, d318384, d318517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d316196 q = 1) (hb : d318385 q = 1) : d318518 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d316196, d318385, d318518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316196, d318385, d318518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83960 (p : Pattern) (ha : d316202 p = 1) (hb : d318391 p = 1) : d318524 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316197 q = 1) (hb : d318386 q = 1) : d318519 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d316197, d318386, d318519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83959 q ha hb
    | true =>
      simp only [d316197, d318386, d318519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d316198 q = 1) (hb : d318387 q = 1) : d318520 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d316198, d318387, d318520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d316198, d318387, d318520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d316199 q = 1) (hb : d318388 q = 1) : d318521 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d316199, d318388, d318521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d316199, d318388, d318521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d316200 q = 1) (hb : d318389 q = 1) : d318522 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d316200, d318389, d318522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d316200, d318389, d318522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d316201 q = 1) (hb : d318390 q = 1) : d318523 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d316201, d318390, d318523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d316201, d318390, d318523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d316202 q = 1) (hb : d318391 q = 1) : d318524 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d316202, d318391, d318524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316202, d318391, d318524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83961 (p : Pattern) (ha : d316208 p = 1) (hb : d318397 p = 1) : d318530 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316203 q = 1) (hb : d318392 q = 1) : d318525 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d316203, d318392, d318525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83960 q ha hb
    | true =>
      simp only [d316203, d318392, d318525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d316204 q = 1) (hb : d318393 q = 1) : d318526 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d316204, d318393, d318526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d316204, d318393, d318526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d316205 q = 1) (hb : d318394 q = 1) : d318527 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d316205, d318394, d318527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d316205, d318394, d318527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d316206 q = 1) (hb : d318395 q = 1) : d318528 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d316206, d318395, d318528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d316206, d318395, d318528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d316207 q = 1) (hb : d318396 q = 1) : d318529 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d316207, d318396, d318529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d316207, d318396, d318529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d316208 q = 1) (hb : d318397 q = 1) : d318530 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d316208, d318397, d318530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316208, d318397, d318530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83962 (p : Pattern) (ha : d316214 p = 1) (hb : d318403 p = 1) : d318536 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316209 q = 1) (hb : d318398 q = 1) : d318531 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d316209, d318398, d318531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83961 q ha hb
    | true =>
      simp only [d316209, d318398, d318531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d316210 q = 1) (hb : d318399 q = 1) : d318532 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d316210, d318399, d318532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d316210, d318399, d318532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d316211 q = 1) (hb : d318400 q = 1) : d318533 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d316211, d318400, d318533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d316211, d318400, d318533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d316212 q = 1) (hb : d318401 q = 1) : d318534 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d316212, d318401, d318534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d316212, d318401, d318534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d316213 q = 1) (hb : d318402 q = 1) : d318535 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d316213, d318402, d318535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d316213, d318402, d318535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d316214 q = 1) (hb : d318403 q = 1) : d318536 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d316214, d318403, d318536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316214, d318403, d318536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83963 (p : Pattern) (ha : d316220 p = 1) (hb : d318409 p = 1) : d318542 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316215 q = 1) (hb : d318404 q = 1) : d318537 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d316215, d318404, d318537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83962 q ha hb
    | true =>
      simp only [d316215, d318404, d318537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d316216 q = 1) (hb : d318405 q = 1) : d318538 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d316216, d318405, d318538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d316216, d318405, d318538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d316217 q = 1) (hb : d318406 q = 1) : d318539 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d316217, d318406, d318539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d316217, d318406, d318539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d316218 q = 1) (hb : d318407 q = 1) : d318540 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d316218, d318407, d318540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d316218, d318407, d318540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d316219 q = 1) (hb : d318408 q = 1) : d318541 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d316219, d318408, d318541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d316219, d318408, d318541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d316220 q = 1) (hb : d318409 q = 1) : d318542 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d316220, d318409, d318542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316220, d318409, d318542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83964 (p : Pattern) (ha : d316226 p = 1) (hb : d318415 p = 1) : d318548 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316221 q = 1) (hb : d318410 q = 1) : d318543 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d316221, d318410, d318543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83963 q ha hb
    | true =>
      simp only [d316221, d318410, d318543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d316222 q = 1) (hb : d318411 q = 1) : d318544 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d316222, d318411, d318544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d316222, d318411, d318544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d316223 q = 1) (hb : d318412 q = 1) : d318545 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d316223, d318412, d318545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d316223, d318412, d318545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d316224 q = 1) (hb : d318413 q = 1) : d318546 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d316224, d318413, d318546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d316224, d318413, d318546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d316225 q = 1) (hb : d318414 q = 1) : d318547 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d316225, d318414, d318547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d316225, d318414, d318547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d316226 q = 1) (hb : d318415 q = 1) : d318548 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d316226, d318415, d318548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316226, d318415, d318548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro83965 (p : Pattern) (ha : d316540 p = 1) (hb : d318553 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d313776 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d313785 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d313805 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d316535 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d316536 q = 1) (hb : d318549 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d316536, d318549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d316536, d318549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d313904 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d316537 q = 1) (hb : d318550 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d316537, d318550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316537, d318550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d316538 q = 1) (hb : d318551 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d316538, d318551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d316538, d318551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d316539 q = 1) (hb : d318552 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d316539, d318552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d316539, d318552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d316540 q = 1) (hb : d318553 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d316540, d318553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d316540, d318553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro83966 (p : Pattern) (ha : d316550 p = 1) (hb : d318558 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d313776 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d313785 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d313805 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d316535 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d316536 q = 1) (hb : d318549 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d316536, d318549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d316536, d318549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d313904 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d316537 q = 1) (hb : d318550 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d316537, d318550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d316537, d318550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d316538 q = 1) (hb : d318551 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d316538, d318551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d316538, d318551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d316539 q = 1) (hb : d318552 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d316539, d318552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d316539, d318552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d313914 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d313919 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d313921 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d316545 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d316546 q = 1) (hb : d318554 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d316546, d318554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d316546, d318554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d313928 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d316547 q = 1) (hb : d318555 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d316547, d318555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d316547, d318555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d316548 q = 1) (hb : d318556 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d316548, d318556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d316548, d318556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d316549 q = 1) (hb : d318557 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d316549, d318557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d316549, d318557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d316550 q = 1) (hb : d318558 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d316550, d318558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d316550, d318558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro83967 (p : Pattern) (ha : d318258 p = 1) (hb : d318565 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d313921 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d316545 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d316546 q = 1) (hb : d318554 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d316546, d318554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d316546, d318554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d313928 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d316547 q = 1) (hb : d318555 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d316547, d318555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d316547, d318555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d316548 q = 1) (hb : d318563 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d316548, d318563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d316548, d318563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d316549 q = 1) (hb : d318564 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d316549, d318564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d316549, d318564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d318258 q = 1) (hb : d318565 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d318258, d318565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d318258, d318565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83968 (p : Pattern) (ha : d318269 p = 1) (hb : d318575 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d314036 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d318264 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d318265 q = 1) (hb : d318571 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d318265, d318571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d318265, d318571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d314114 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d318266 q = 1) (hb : d318572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d318266, d318572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d318266, d318572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d318267 q = 1) (hb : d318573 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d318267, d318573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d318267, d318573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d318268 q = 1) (hb : d318574 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d318268, d318574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d318268, d318574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d318269 q = 1) (hb : d318575 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d318269, d318575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d318269, d318575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83969 (p : Pattern) (ha : d318275 p = 1) (hb : d318581 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d313768 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316551 q = 1) (hb : d318559 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d316551, d318559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83965 q ha hb
    | true =>
      simp only [d316551, d318559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83966 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d313946 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d316552 q = 1) (hb : d318560 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d316552, d318560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d316552, d318560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d318256 q = 1) (hb : d318561 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d318256, d318561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d318256, d318561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d318257 q = 1) (hb : d318562 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d318257, d318562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d318257, d318562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d318259 q = 1) (hb : d318566 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d318259, d318566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d318259, d318566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83967 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d313955 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d318260 q = 1) (hb : d318567 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d318260, d318567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d318260, d318567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d318261 q = 1) (hb : d318568 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d318261, d318568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d318261, d318568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d318262 q = 1) (hb : d318569 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d318262, d318569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d318262, d318569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d318263 q = 1) (hb : d318570 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d318263, d318570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d318263, d318570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d318270 q = 1) (hb : d318576 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d318270, d318576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d318270, d318576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83968 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d314130 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d318271 q = 1) (hb : d318577 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d318271, d318577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d318271, d318577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d318272 q = 1) (hb : d318578 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d318272, d318578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d318272, d318578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d318273 q = 1) (hb : d318579 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d318273, d318579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d318273, d318579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d318274 q = 1) (hb : d318580 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d318274, d318580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d318274, d318580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d318275 q = 1) (hb : d318581 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d318275, d318581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d318275, d318581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro83970 (p : Pattern) (ha : d318281 p = 1) (hb : d318587 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d318276 q = 1) (hb : d318582 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d318276, d318582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d318276, d318582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83969 q ha hb
  have h2 (q : Pattern) (ha : d318277 q = 1) (hb : d318583 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d318277, d318583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d318277, d318583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d318278 q = 1) (hb : d318584 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d318278, d318584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d318278, d318584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d318279 q = 1) (hb : d318585 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d318279, d318585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d318279, d318585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d318280 q = 1) (hb : d318586 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d318280, d318586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d318280, d318586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d318281 q = 1) (hb : d318587 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d318281, d318587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d318281, d318587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83971 (p : Pattern) (ha : d316827 p = 1) (hb : d318595 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d314255 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d314264 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d314284 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d316822 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d316823 q = 1) (hb : d318591 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d316823, d318591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d316823, d318591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d314401 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d316824 q = 1) (hb : d318592 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d316824, d318592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d316824, d318592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d316825 q = 1) (hb : d318593 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d316825, d318593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d316825, d318593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d316826 q = 1) (hb : d318594 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d316826, d318594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d316826, d318594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d316827 q = 1) (hb : d318595 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d316827, d318595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d316827, d318595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro83972 (p : Pattern) (ha : d316837 p = 1) (hb : d318600 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d314255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d314264 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d314284 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d316822 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d316823 q = 1) (hb : d318591 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d316823, d318591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d316823, d318591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d314401 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d316824 q = 1) (hb : d318592 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d316824, d318592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d316824, d318592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d316825 q = 1) (hb : d318593 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d316825, d318593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d316825, d318593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d316826 q = 1) (hb : d318594 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d316826, d318594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d316826, d318594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d314411 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d314416 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d314418 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d316832 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d316833 q = 1) (hb : d318596 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d316833, d318596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d316833, d318596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d314425 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d316834 q = 1) (hb : d318597 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d316834, d318597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d316834, d318597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d316835 q = 1) (hb : d318598 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d316835, d318598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d316835, d318598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d316836 q = 1) (hb : d318599 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d316836, d318599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d316836, d318599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d316837 q = 1) (hb : d318600 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d316837, d318600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d316837, d318600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro83973 (p : Pattern) (ha : d318287 p = 1) (hb : d318607 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d314418 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d316832 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d316833 q = 1) (hb : d318596 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d316833, d318596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d316833, d318596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d314425 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d316834 q = 1) (hb : d318597 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d316834, d318597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d316834, d318597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d316835 q = 1) (hb : d318605 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d316835, d318605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d316835, d318605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d316836 q = 1) (hb : d318606 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d316836, d318606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d316836, d318606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d318287 q = 1) (hb : d318607 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d318287, d318607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d318287, d318607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83974 (p : Pattern) (ha : d318298 p = 1) (hb : d318617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d314533 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d318293 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d318294 q = 1) (hb : d318613 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d318294, d318613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d318294, d318613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d314622 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d318295 q = 1) (hb : d318614 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d318295, d318614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d318295, d318614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d318296 q = 1) (hb : d318615 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d318296, d318615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d318296, d318615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d318297 q = 1) (hb : d318616 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d318297, d318616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d318297, d318616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d318298 q = 1) (hb : d318617 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d318298, d318617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d318298, d318617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83975 (p : Pattern) (ha : d318304 p = 1) (hb : d318623 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d314247 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d316838 q = 1) (hb : d318601 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d316838, d318601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83971 q ha hb
    | true =>
      simp only [d316838, d318601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83972 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d314443 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d316839 q = 1) (hb : d318602 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d316839, d318602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d316839, d318602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d318285 q = 1) (hb : d318603 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d318285, d318603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d318285, d318603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d318286 q = 1) (hb : d318604 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d318286, d318604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d318286, d318604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d318288 q = 1) (hb : d318608 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d318288, d318608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d318288, d318608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83973 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d314452 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d318289 q = 1) (hb : d318609 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d318289, d318609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d318289, d318609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d318290 q = 1) (hb : d318610 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d318290, d318610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d318290, d318610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d318291 q = 1) (hb : d318611 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d318291, d318611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d318291, d318611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d318292 q = 1) (hb : d318612 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d318292, d318612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d318292, d318612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d318299 q = 1) (hb : d318618 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d318299, d318618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d318299, d318618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83974 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d314638 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d318300 q = 1) (hb : d318619 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d318300, d318619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d318300, d318619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d318301 q = 1) (hb : d318620 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d318301, d318620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d318301, d318620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d318302 q = 1) (hb : d318621 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d318302, d318621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d318302, d318621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d318303 q = 1) (hb : d318622 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d318303, d318622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d318303, d318622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d318304 q = 1) (hb : d318623 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d318304, d318623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d318304, d318623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro83976 (p : Pattern) (ha : d318310 p = 1) (hb : d318629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d318305 q = 1) (hb : d318624 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d318305, d318624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d318305, d318624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83975 q ha hb
  have h2 (q : Pattern) (ha : d318306 q = 1) (hb : d318625 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d318306, d318625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d318306, d318625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d318307 q = 1) (hb : d318626 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d318307, d318626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d318307, d318626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d318308 q = 1) (hb : d318627 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d318308, d318627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d318308, d318627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d318309 q = 1) (hb : d318628 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d318309, d318628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d318309, d318628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d318310 q = 1) (hb : d318629 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d318310, d318629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d318310, d318629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83977 (p : Pattern) (ha : d317132 p = 1) (hb : d318638 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d314750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d314759 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d314777 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d317127 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d317128 q = 1) (hb : d318634 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d317128, d318634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d317128, d318634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d314880 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d317129 q = 1) (hb : d318635 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d317129, d318635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d317129, d318635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d317130 q = 1) (hb : d318636 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d317130, d318636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d317130, d318636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d317131 q = 1) (hb : d318637 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d317131, d318637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d317131, d318637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d317132 q = 1) (hb : d318638 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d317132, d318638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d317132, d318638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro83978 (p : Pattern) (ha : d317142 p = 1) (hb : d318643 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d314750 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d314759 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d314777 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d317127 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d317128 q = 1) (hb : d318634 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d317128, d318634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d317128, d318634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d314880 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d317129 q = 1) (hb : d318635 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d317129, d318635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d317129, d318635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d317130 q = 1) (hb : d318636 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d317130, d318636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d317130, d318636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d317131 q = 1) (hb : d318637 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d317131, d318637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d317131, d318637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d314890 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d314895 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d314897 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d317137 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d317138 q = 1) (hb : d318639 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d317138, d318639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d317138, d318639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d314904 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d317139 q = 1) (hb : d318640 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d317139, d318640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d317139, d318640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d317140 q = 1) (hb : d318641 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d317140, d318641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d317140, d318641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d317141 q = 1) (hb : d318642 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d317141, d318642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d317141, d318642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d317142 q = 1) (hb : d318643 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d317142, d318643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d317142, d318643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro83979 (p : Pattern) (ha : d318317 p = 1) (hb : d318650 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d314897 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d317137 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d317138 q = 1) (hb : d318639 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d317138, d318639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d317138, d318639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d314904 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d317139 q = 1) (hb : d318640 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d317139, d318640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d317139, d318640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d317140 q = 1) (hb : d318648 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d317140, d318648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d317140, d318648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d317141 q = 1) (hb : d318649 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d317141, d318649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d317141, d318649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d318317 q = 1) (hb : d318650 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d318317, d318650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d318317, d318650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83980 (p : Pattern) (ha : d318355 p = 1) (hb : d318660 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d315002 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d318350 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d318351 q = 1) (hb : d318656 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d318351, d318656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d318351, d318656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d315083 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d318352 q = 1) (hb : d318657 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d318352, d318657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d318352, d318657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d318353 q = 1) (hb : d318658 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d318353, d318658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d318353, d318658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d318354 q = 1) (hb : d318659 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d318354, d318659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d318354, d318659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d318355 q = 1) (hb : d318660 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d318355, d318660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d318355, d318660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83981 (p : Pattern) (ha : d318361 p = 1) (hb : d318666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d314742 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d317143 q = 1) (hb : d318644 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d317143, d318644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83977 q ha hb
    | true =>
      simp only [d317143, d318644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83978 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d314922 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d317144 q = 1) (hb : d318645 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d317144, d318645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d317144, d318645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d318315 q = 1) (hb : d318646 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d318315, d318646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d318315, d318646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d318316 q = 1) (hb : d318647 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d318316, d318647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d318316, d318647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d318318 q = 1) (hb : d318651 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d318318, d318651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d318318, d318651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83979 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d314931 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d318319 q = 1) (hb : d318652 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d318319, d318652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d318319, d318652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d318320 q = 1) (hb : d318653 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d318320, d318653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d318320, d318653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d318321 q = 1) (hb : d318654 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d318321, d318654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d318321, d318654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d318322 q = 1) (hb : d318655 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d318322, d318655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d318322, d318655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d318356 q = 1) (hb : d318661 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d318356, d318661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d318356, d318661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83980 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d315099 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d318357 q = 1) (hb : d318662 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d318357, d318662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d318357, d318662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d318358 q = 1) (hb : d318663 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d318358, d318663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d318358, d318663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d318359 q = 1) (hb : d318664 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d318359, d318664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d318359, d318664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d318360 q = 1) (hb : d318665 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d318360, d318665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d318360, d318665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d318361 q = 1) (hb : d318666 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d318361, d318666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d318361, d318666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro83982 (p : Pattern) (ha : d318367 p = 1) (hb : d318672 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d318362 q = 1) (hb : d318667 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d318362, d318667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d318362, d318667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83981 q ha hb
  have h2 (q : Pattern) (ha : d318363 q = 1) (hb : d318668 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d318363, d318668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d318363, d318668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d318364 q = 1) (hb : d318669 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d318364, d318669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d318364, d318669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d318365 q = 1) (hb : d318670 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d318365, d318670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d318365, d318670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d318366 q = 1) (hb : d318671 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d318366, d318671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d318366, d318671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d318367 q = 1) (hb : d318672 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d318367, d318672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d318367, d318672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro83983 (p : Pattern) (ha : d318373 p = 1) (hb : d318678 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d318255 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d318282 q = 1) (hb : d318588 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d318282, d318588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d318282, d318588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83970 q ha hb
  have h3 (q : Pattern) (ha : d318283 q = 1) (hb : d318589 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d318283, d318589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d318283, d318589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d318284 q = 1) (hb : d318590 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d318284, d318590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318284, d318590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d318311 q = 1) (hb : d318630 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d318311, d318630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d318311, d318630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83976 q ha hb
  have h6 (q : Pattern) (ha : d318312 q = 1) (hb : d318631 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d318312, d318631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d318312, d318631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d318313 q = 1) (hb : d318632 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d318313, d318632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d318313, d318632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d318314 q = 1) (hb : d318633 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d318314, d318633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d318314, d318633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d318368 q = 1) (hb : d318673 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d318368, d318673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d318368, d318673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83982 q ha hb
  have h10 (q : Pattern) (ha : d318369 q = 1) (hb : d318674 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d318369, d318674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d318369, d318674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d318370 q = 1) (hb : d318675 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d318370, d318675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d318370, d318675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d318371 q = 1) (hb : d318676 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d318371, d318676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d318371, d318676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d318372 q = 1) (hb : d318677 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d318372, d318677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d318372, d318677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d318373 q = 1) (hb : d318678 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d318373, d318678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d318373, d318678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h14 p ha hb
theorem andIntro83984 (p : Pattern) (ha : d318379 p = 1) (hb : d318684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d318374 q = 1) (hb : d318679 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d318374, d318679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83983 q ha hb
    | true =>
      simp only [d318374, d318679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d318375 q = 1) (hb : d318680 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d318375, d318680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d318375, d318680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d318376 q = 1) (hb : d318681 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d318376, d318681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d318376, d318681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d318377 q = 1) (hb : d318682 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d318377, d318682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d318377, d318682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d318378 q = 1) (hb : d318683 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d318378, d318683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d318378, d318683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d318379 q = 1) (hb : d318684 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d318379, d318684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d318379, d318684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro83985 (p : Pattern) (ha : d318385 p = 1) (hb : d318690 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d318380 q = 1) (hb : d318685 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d318380, d318685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83984 q ha hb
    | true =>
      simp only [d318380, d318685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d318381 q = 1) (hb : d318686 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d318381, d318686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d318381, d318686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d318382 q = 1) (hb : d318687 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d318382, d318687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d318382, d318687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d318383 q = 1) (hb : d318688 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d318383, d318688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d318383, d318688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d318384 q = 1) (hb : d318689 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d318384, d318689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d318384, d318689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d318385 q = 1) (hb : d318690 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d318385, d318690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d318385, d318690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro83986 (p : Pattern) (ha : d318391 p = 1) (hb : d318696 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d318386 q = 1) (hb : d318691 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d318386, d318691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83985 q ha hb
    | true =>
      simp only [d318386, d318691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d318387 q = 1) (hb : d318692 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d318387, d318692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d318387, d318692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d318388 q = 1) (hb : d318693 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d318388, d318693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d318388, d318693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d318389 q = 1) (hb : d318694 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d318389, d318694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d318389, d318694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d318390 q = 1) (hb : d318695 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d318390, d318695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d318390, d318695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d318391 q = 1) (hb : d318696 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d318391, d318696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d318391, d318696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro83987 (p : Pattern) (ha : d318397 p = 1) (hb : d318702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d318392 q = 1) (hb : d318697 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d318392, d318697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83986 q ha hb
    | true =>
      simp only [d318392, d318697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d318393 q = 1) (hb : d318698 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d318393, d318698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d318393, d318698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d318394 q = 1) (hb : d318699 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d318394, d318699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d318394, d318699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d318395 q = 1) (hb : d318700 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d318395, d318700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d318395, d318700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d318396 q = 1) (hb : d318701 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d318396, d318701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d318396, d318701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d318397 q = 1) (hb : d318702 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d318397, d318702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d318397, d318702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro83988 (p : Pattern) (ha : d318403 p = 1) (hb : d318708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d318398 q = 1) (hb : d318703 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d318398, d318703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83987 q ha hb
    | true =>
      simp only [d318398, d318703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d318399 q = 1) (hb : d318704 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d318399, d318704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d318399, d318704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d318400 q = 1) (hb : d318705 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d318400, d318705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d318400, d318705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d318401 q = 1) (hb : d318706 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d318401, d318706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d318401, d318706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d318402 q = 1) (hb : d318707 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d318402, d318707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d318402, d318707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d318403 q = 1) (hb : d318708 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d318403, d318708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d318403, d318708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro83989 (p : Pattern) (ha : d318409 p = 1) (hb : d318714 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d318404 q = 1) (hb : d318709 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d318404, d318709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83988 q ha hb
    | true =>
      simp only [d318404, d318709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d318405 q = 1) (hb : d318710 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d318405, d318710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d318405, d318710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d318406 q = 1) (hb : d318711 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d318406, d318711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d318406, d318711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d318407 q = 1) (hb : d318712 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d318407, d318712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d318407, d318712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d318408 q = 1) (hb : d318713 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d318408, d318713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d318408, d318713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d318409 q = 1) (hb : d318714 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d318409, d318714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d318409, d318714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro83990 (p : Pattern) (ha : d318415 p = 1) (hb : d318720 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d318410 q = 1) (hb : d318715 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d318410, d318715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83989 q ha hb
    | true =>
      simp only [d318410, d318715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d318411 q = 1) (hb : d318716 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d318411, d318716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d318411, d318716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d318412 q = 1) (hb : d318717 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d318412, d318717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d318412, d318717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d318413 q = 1) (hb : d318718 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d318413, d318718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d318413, d318718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d318414 q = 1) (hb : d318719 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d318414, d318719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d318414, d318719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d318415 q = 1) (hb : d318720 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d318415, d318720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d318415, d318720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro83991 (p : Pattern) (ha : d33220 p = 1) (hb : d277740 p = 1) : d277747 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33215 q = 1) (hb : d277739 q = 1) : d277742 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d33215, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81703 q ha hb
    | true =>
      simp only [d33215, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d33216 q = 1) (hb : d277740 q = 1) : d277743 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d33216, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33216, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20 q = 1) (hb : d277740 q = 1) : d20 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d33217 q = 1) (hb : d277740 q = 1) : d277744 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d33217, d277744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33217, d277744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21 q = 1) (hb : d277740 q = 1) : d21 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d33218 q = 1) (hb : d277740 q = 1) : d277745 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d33218, d277745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33218, d277745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d33219 q = 1) (hb : d277740 q = 1) : d277746 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d33219, d277746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33219, d277746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23 q = 1) (hb : d277740 q = 1) : d23 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d33220 q = 1) (hb : d277740 q = 1) : d277747 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d33220, d277747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33220, d277747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro83992 (p : Pattern) (ha : d33226 p = 1) (hb : d277740 p = 1) : d277753 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33221 q = 1) (hb : d277740 q = 1) : d277748 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33221, d277748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83991 q ha hb
    | true =>
      simp only [d33221, d277748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33222 q = 1) (hb : d277740 q = 1) : d277749 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33222, d277749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33222, d277749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33223 q = 1) (hb : d277740 q = 1) : d277750 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33223, d277750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33223, d277750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33224 q = 1) (hb : d277740 q = 1) : d277751 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33224, d277751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33224, d277751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d277740 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d33225 q = 1) (hb : d277740 q = 1) : d277752 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33225, d277752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33225, d277752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d277740 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d33226 q = 1) (hb : d277740 q = 1) : d277753 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33226, d277753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33226, d277753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83993 (p : Pattern) (ha : d33232 p = 1) (hb : d277740 p = 1) : d277759 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d277740 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33227 q = 1) (hb : d277740 q = 1) : d277754 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33227, d277754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83992 q ha hb
    | true =>
      simp only [d33227, d277754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33228 q = 1) (hb : d277740 q = 1) : d277755 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33228, d277755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33228, d277755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33229 q = 1) (hb : d277740 q = 1) : d277756 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33229, d277756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33229, d277756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d277740 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d33230 q = 1) (hb : d277740 q = 1) : d277757 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33230, d277757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33230, d277757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d277740 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d33231 q = 1) (hb : d277740 q = 1) : d277758 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33231, d277758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33231, d277758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33232 q = 1) (hb : d277740 q = 1) : d277759 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33232, d277759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33232, d277759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro83994 (p : Pattern) (ha : d33238 p = 1) (hb : d277740 p = 1) : d277765 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33233 q = 1) (hb : d277740 q = 1) : d277760 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83993 q ha hb
    | true =>
      simp only [d33233, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33234 q = 1) (hb : d277740 q = 1) : d277761 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d277740 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33235 q = 1) (hb : d277740 q = 1) : d277762 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33235, d277762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33235, d277762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33236 q = 1) (hb : d277740 q = 1) : d277763 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33236, d277763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33236, d277763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33237 q = 1) (hb : d277740 q = 1) : d277764 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33237, d277764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33237, d277764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33238 q = 1) (hb : d277740 q = 1) : d277765 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33238, d277765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33238, d277765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro83995 (p : Pattern) (ha : d265915 p = 1) (hb : d277740 p = 1) : d277771 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d277740 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d277740 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d277740 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33239 q = 1) (hb : d277740 q = 1) : d277766 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33239, d277766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83994 q ha hb
    | true =>
      simp only [d33239, d277766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d265911 q = 1) (hb : d277740 q = 1) : d277767 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265911, d277767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265911, d277767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d277740 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d265912 q = 1) (hb : d277740 q = 1) : d277768 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265912, d277768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d265912, d277768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265913 q = 1) (hb : d277740 q = 1) : d277769 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265913, d277769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d265913, d277769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d265914 q = 1) (hb : d277740 q = 1) : d277770 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265914, d277770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265914, d277770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d265915 q = 1) (hb : d277740 q = 1) : d277771 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265915, d277771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265915, d277771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro83996 (p : Pattern) (ha : d33245 p = 1) (hb : d277740 p = 1) : d277772 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33233 q = 1) (hb : d277740 q = 1) : d277760 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33233, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83993 q ha hb
    | true =>
      simp only [d33233, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33234 q = 1) (hb : d277740 q = 1) : d277761 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33234, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33234, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d277740 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33235 q = 1) (hb : d277740 q = 1) : d277762 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33235, d277762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33235, d277762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33236 q = 1) (hb : d277740 q = 1) : d277763 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33236, d277763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33236, d277763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33237 q = 1) (hb : d277740 q = 1) : d277764 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33237, d277764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33237, d277764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33245 q = 1) (hb : d277740 q = 1) : d277772 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33245, d277772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33245, d277772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro83997 (p : Pattern) (ha : d265920 p = 1) (hb : d277740 p = 1) : d277778 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d277740 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d277740 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d277740 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d33239 q = 1) (hb : d277740 q = 1) : d277766 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33239, d277766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83994 q ha hb
    | true =>
      simp only [d33239, d277766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265911 q = 1) (hb : d277740 q = 1) : d277767 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265911, d277767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d265911, d277767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d277740 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d265912 q = 1) (hb : d277740 q = 1) : d277768 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265912, d277768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d265912, d277768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265913 q = 1) (hb : d277740 q = 1) : d277769 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265913, d277769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265913, d277769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d265914 q = 1) (hb : d277740 q = 1) : d277770 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265914, d277770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265914, d277770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d277740 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d277740 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d277740 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d33246 q = 1) (hb : d277740 q = 1) : d277773 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33246, d277773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83996 q ha hb
    | true =>
      simp only [d33246, d277773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d265916 q = 1) (hb : d277740 q = 1) : d277774 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265916, d277774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d265916, d277774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d277740 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d265917 q = 1) (hb : d277740 q = 1) : d277775 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265917, d277775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d265917, d277775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d265918 q = 1) (hb : d277740 q = 1) : d277776 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265918, d277776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d265918, d277776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d265919 q = 1) (hb : d277740 q = 1) : d277777 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265919, d277777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d265919, d277777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d265920 q = 1) (hb : d277740 q = 1) : d277778 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265920, d277778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d265920, d277778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro83998 (p : Pattern) (ha : d265927 p = 1) (hb : d277740 p = 1) : d277785 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d277740 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33246 q = 1) (hb : d277740 q = 1) : d277773 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33246, d277773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83996 q ha hb
    | true =>
      simp only [d33246, d277773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d265916 q = 1) (hb : d277740 q = 1) : d277774 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265916, d277774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d265916, d277774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d277740 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265917 q = 1) (hb : d277740 q = 1) : d277775 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265917, d277775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d265917, d277775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d265925 q = 1) (hb : d277740 q = 1) : d277783 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265925, d277783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265925, d277783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265926 q = 1) (hb : d277740 q = 1) : d277784 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265926, d277784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265926, d277784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265927 q = 1) (hb : d277740 q = 1) : d277785 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265927, d277785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265927, d277785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro83999 (p : Pattern) (ha : d33269 p = 1) (hb : d277740 p = 1) : d277796 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33264 q = 1) (hb : d277740 q = 1) : d277791 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33264, d277791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33264, d277791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83991 q ha hb
  have h2 (q : Pattern) (ha : d33221 q = 1) (hb : d277740 q = 1) : d277748 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33221, d277748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83991 q ha hb
    | true =>
      simp only [d33221, d277748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33265 q = 1) (hb : d277740 q = 1) : d277792 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33265, d277792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33265, d277792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33222 q = 1) (hb : d277740 q = 1) : d277749 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33222, d277749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33222, d277749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33266 q = 1) (hb : d277740 q = 1) : d277793 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33266, d277793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33266, d277793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33267 q = 1) (hb : d277740 q = 1) : d277794 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33267, d277794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33267, d277794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d277740 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d33268 q = 1) (hb : d277740 q = 1) : d277795 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33268, d277795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33268, d277795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d277740 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d33269 q = 1) (hb : d277740 q = 1) : d277796 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33269, d277796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33269, d277796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
end NetHack.Soko22Hazard87
