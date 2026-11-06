import NetHack.Soko22Hazard87.EqIntroBlocks0073
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro18500 (p : Pattern) (selected : d194700 p = 0) : d195488 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194684 q = 0) : d195481 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194684, d195481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18496 q selected
    | true =>
      simp only [d194684, d195481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18497 q selected
  have h2 (q : Pattern) (selected : d194693 q = 0) : d195482 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194693, d195482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18499 q selected
    | true =>
      simp only [d194693, d195482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d194694 q = 0) : d195483 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194694, d195483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d194694, d195483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d194695 q = 0) : d195482 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194695, d195482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18497 q selected
    | true =>
      simp only [d194695, d195482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194696 q = 0) : d195484 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194696, d195484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194696, d195484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d194697 q = 0) : d195485 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194697, d195485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194697, d195485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d194698 q = 0) : d195486 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194698, d195486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194698, d195486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d194699 q = 0) : d195487 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194699, d195487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194699, d195487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d194700 q = 0) : d195488 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194700, d195488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194700, d195488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro18501 (p : Pattern) (selected : d194706 p = 0) : d195494 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194585 q = 0) : d195393 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194585, d195393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194585, d195393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18478 q selected
  have h2 (q : Pattern) (selected : d194586 q = 0) : d195394 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194586, d195394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d194586, d195394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d194594 q = 0) : d195402 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194594, d195402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18478 q selected
    | true =>
      simp only [d194594, d195402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18480 q selected
  have h4 (q : Pattern) (selected : d194595 q = 0) : d195403 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194595, d195403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194595, d195403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194596 q = 0) : d195404 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194596, d195404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194596, d195404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194655 q = 0) : d195452 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194655, d195452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18487 q selected
    | true =>
      simp only [d194655, d195452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18492 q selected
  have h7 (q : Pattern) (selected : d194657 q = 0) : d195454 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194657, d195454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18493 q selected
    | true =>
      simp only [d194657, d195454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d194658 q = 0) : d195455 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194658, d195455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d194658, d195455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d194659 q = 0) : d195456 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194659, d195456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d194659, d195456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d194660 q = 0) : d195457 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194660, d195457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d194660, d195457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d194664 q = 0) : d195461 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194664, d195461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194664, d195461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18494 q selected
  have h12 (q : Pattern) (selected : d194665 q = 0) : d195462 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194665, d195462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d194665, d195462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d194666 q = 0) : d195463 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194666, d195463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d194666, d195463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d194667 q = 0) : d195464 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194667, d195464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d194667, d195464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d194668 q = 0) : d195465 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194668, d195465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d194668, d195465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d194701 q = 0) : d195489 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194701, d195489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194701, d195489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18500 q selected
  have h17 (q : Pattern) (selected : d194702 q = 0) : d195490 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194702, d195490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d194702, d195490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d194703 q = 0) : d195491 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194703, d195491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d194703, d195491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d194704 q = 0) : d195492 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194704, d195492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d194704, d195492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d194705 q = 0) : d195493 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194705, d195493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d194705, d195493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d194706 q = 0) : d195494 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194706, d195494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d194706, d195494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro18502 (p : Pattern) (selected : d194712 p = 0) : d195500 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194707 q = 0) : d195495 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194707, d195495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194707, d195495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18501 q selected
  have h2 (q : Pattern) (selected : d194708 q = 0) : d195496 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194708, d195496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194708, d195496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194709 q = 0) : d195497 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194709, d195497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194709, d195497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d194710 q = 0) : d195498 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194710, d195498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194710, d195498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d194711 q = 0) : d195499 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194711, d195499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194711, d195499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194712 q = 0) : d195500 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194712, d195500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194712, d195500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18503 (p : Pattern) (selected : d194717 p = 0) : d195505 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95190 q = 0) : d96601 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95190, d96601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6093 q selected
    | true =>
      simp only [d95190, d96601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95191 q = 0) : d96602 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95191, d96602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95191, d96602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194714 q = 0) : d195502 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194714, d195502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194714, d195502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194715 q = 0) : d195503 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194715, d195503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194715, d195503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194716 q = 0) : d195504 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194716, d195504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194716, d195504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d194717 q = 0) : d195505 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194717, d195505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194717, d195505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18504 (p : Pattern) (selected : d194723 p = 0) : d195511 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194718 q = 0) : d195506 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194718, d195506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18503 q selected
    | true =>
      simp only [d194718, d195506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d194719 q = 0) : d195507 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194719, d195507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194719, d195507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194720 q = 0) : d195508 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194720, d195508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194720, d195508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194721 q = 0) : d195509 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194721, d195509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194721, d195509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d194722 q = 0) : d195510 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194722, d195510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194722, d195510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194723 q = 0) : d195511 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194723, d195511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194723, d195511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18505 (p : Pattern) (selected : d194726 p = 0) : d195514 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95190 q = 0) : d96601 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95190, d96601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6093 q selected
    | true =>
      simp only [d95190, d96601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95191 q = 0) : d96602 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95191, d96602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95191, d96602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194714 q = 0) : d195502 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194714, d195502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194714, d195502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194715 q = 0) : d195503 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194715, d195503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194715, d195503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194716 q = 0) : d195504 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194716, d195504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194716, d195504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d194726 q = 0) : d195514 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194726, d195514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d194726, d195514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18506 (p : Pattern) (selected : d194732 p = 0) : d195520 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194718 q = 0) : d195506 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194718, d195506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18503 q selected
    | true =>
      simp only [d194718, d195506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d194719 q = 0) : d195507 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194719, d195507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194719, d195507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194720 q = 0) : d195508 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194720, d195508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194720, d195508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194721 q = 0) : d195509 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194721, d195509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194721, d195509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d194722 q = 0) : d195510 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194722, d195510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194722, d195510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194727 q = 0) : d195515 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194727, d195515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18505 q selected
    | true =>
      simp only [d194727, d195515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d194728 q = 0) : d195516 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194728, d195516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194728, d195516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d194729 q = 0) : d195517 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194729, d195517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d194729, d195517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d194730 q = 0) : d195518 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194730, d195518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194730, d195518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d194731 q = 0) : d195519 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194731, d195519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194731, d195519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d194732 q = 0) : d195520 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194732, d195520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d194732, d195520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro18507 (p : Pattern) (selected : d194737 p = 0) : d195525 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95190 q = 0) : d96601 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95190, d96601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6093 q selected
    | true =>
      simp only [d95190, d96601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95191 q = 0) : d96602 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95191, d96602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95191, d96602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194714 q = 0) : d195502 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194714, d195502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194714, d195502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194715 q = 0) : d195503 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194715, d195503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194715, d195503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194736 q = 0) : d195524 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194736, d195524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194736, d195524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194737 q = 0) : d195525 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194737, d195525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194737, d195525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18508 (p : Pattern) (selected : d194744 p = 0) : d195532 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95190 q = 0) : d96601 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95190, d96601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6093 q selected
    | true =>
      simp only [d95190, d96601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95191 q = 0) : d96602 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95191, d96602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95191, d96602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194714 q = 0) : d195502 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194714, d195502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194714, d195502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194742 q = 0) : d195530 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194742, d195530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194742, d195530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d194743 q = 0) : d195531 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194743, d195531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194743, d195531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d194744 q = 0) : d195532 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194744, d195532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194744, d195532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18509 (p : Pattern) (selected : d194752 p = 0) : d195540 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194748 q = 0) : d195536 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d194748, d195536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6091 q selected
    | true =>
      simp only [d194748, d195536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15033 q selected
  have h2 (q : Pattern) (selected : d194749 q = 0) : d195537 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d194749, d195537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194749, d195537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194750 q = 0) : d195538 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d194750, d195538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194750, d195538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95123 q = 0) : d96534 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95123, d96534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6077 q selected
    | true =>
      simp only [d95123, d96534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6078 q selected
  have h5 (q : Pattern) (selected : d95124 q = 0) : d96535 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95124, d96535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95124, d96535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95125 q = 0) : d96536 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95125, d96536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95125, d96536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d194751 q = 0) : d195539 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d194751, d195539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194751, d195539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d194752 q = 0) : d195540 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d194752, d195540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d194752, d195540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro18510 (p : Pattern) (selected : d194758 p = 0) : d195546 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194753 q = 0) : d195541 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194753, d195541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18509 q selected
    | true =>
      simp only [d194753, d195541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d194754 q = 0) : d195542 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194754, d195542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194754, d195542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95190 q = 0) : d96601 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95190, d96601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6093 q selected
    | true =>
      simp only [d95190, d96601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95191 q = 0) : d96602 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95191, d96602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95191, d96602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d194755 q = 0) : d195543 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194755, d195543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194755, d195543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194756 q = 0) : d195544 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194756, d195544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d194756, d195544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d194757 q = 0) : d195545 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194757, d195545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d194757, d195545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d194758 q = 0) : d195546 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194758, d195546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194758, d195546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro18511 (p : Pattern) (selected : d194761 p = 0) : d96600 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95201 q = 0) : d96534 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95201, d96534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6096 q selected
    | true =>
      simp only [d95201, d96534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6097 q selected
  have h2 (q : Pattern) (selected : d95202 q = 0) : d96535 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95202, d96535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95202, d96535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95203 q = 0) : d96536 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95203, d96536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95203, d96536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d194760 q = 0) : d96599 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d194760, d96599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194760, d96599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194761 q = 0) : d96600 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d194761, d96600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194761, d96600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro18512 (p : Pattern) (selected : d194767 p = 0) : d195505 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194762 q = 0) : d96601 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194762, d96601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18511 q selected
    | true =>
      simp only [d194762, d96601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d194763 q = 0) : d96602 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194763, d96602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194763, d96602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194764 q = 0) : d195502 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194764, d195502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194764, d195502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194765 q = 0) : d195503 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194765, d195503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194765, d195503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194766 q = 0) : d195504 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194766, d195504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194766, d195504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d194767 q = 0) : d195505 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194767, d195505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194767, d195505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18513 (p : Pattern) (selected : d194774 p = 0) : d195553 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194738 q = 0) : d195526 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194738, d195526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18507 q selected
    | true =>
      simp only [d194738, d195526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d194739 q = 0) : d195527 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194739, d195527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194739, d195527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194740 q = 0) : d195528 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194740, d195528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194740, d195528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194741 q = 0) : d195529 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194741, d195529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194741, d195529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d194745 q = 0) : d195533 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194745, d195533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18508 q selected
    | true =>
      simp only [d194745, d195533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d194746 q = 0) : d195534 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194746, d195534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194746, d195534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d194747 q = 0) : d195535 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194747, d195535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d194747, d195535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d194759 q = 0) : d195547 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194759, d195547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18510 q selected
    | true =>
      simp only [d194759, d195547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18503 q selected
  have h9 (q : Pattern) (selected : d194768 q = 0) : d195506 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194768, d195506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18512 q selected
    | true =>
      simp only [d194768, d195506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d194769 q = 0) : d195548 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194769, d195548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d194769, d195548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d194718 q = 0) : d195506 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194718, d195506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18503 q selected
    | true =>
      simp only [d194718, d195506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d194770 q = 0) : d195549 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194770, d195549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d194770, d195549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d194771 q = 0) : d195550 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194771, d195550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d194771, d195550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d194772 q = 0) : d195551 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194772, d195551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d194772, d195551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d194773 q = 0) : d195552 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194773, d195552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194773, d195552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d194774 q = 0) : d195553 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194774, d195553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194774, d195553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro18514 (p : Pattern) (selected : d194775 p = 0) : d195554 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95190 q = 0) : d96601 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95190, d96601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6093 q selected
    | true =>
      simp only [d95190, d96601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95191 q = 0) : d96602 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95191, d96602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95191, d96602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194714 q = 0) : d195502 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194714, d195502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194714, d195502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194715 q = 0) : d195503 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194715, d195503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194715, d195503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194736 q = 0) : d195524 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194736, d195524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194736, d195524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194775 q = 0) : d195554 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194775, d195554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d194775, d195554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18515 (p : Pattern) (selected : d194780 p = 0) : d195559 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95190 q = 0) : d96601 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95190, d96601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6093 q selected
    | true =>
      simp only [d95190, d96601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95191 q = 0) : d96602 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95191, d96602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95191, d96602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194714 q = 0) : d195502 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194714, d195502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194714, d195502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194742 q = 0) : d195530 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194742, d195530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194742, d195530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d194743 q = 0) : d195531 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194743, d195531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194743, d195531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d194780 q = 0) : d195559 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194780, d195559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d194780, d195559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18516 (p : Pattern) (selected : d194784 p = 0) : d195563 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194753 q = 0) : d195541 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194753, d195541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18509 q selected
    | true =>
      simp only [d194753, d195541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d194754 q = 0) : d195542 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194754, d195542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194754, d195542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95190 q = 0) : d96601 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95190, d96601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6093 q selected
    | true =>
      simp only [d95190, d96601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95191 q = 0) : d96602 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95191, d96602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95191, d96602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d194755 q = 0) : d195543 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194755, d195543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194755, d195543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194756 q = 0) : d195544 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194756, d195544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d194756, d195544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d194757 q = 0) : d195545 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194757, d195545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d194757, d195545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d194784 q = 0) : d195563 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194784, d195563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d194784, d195563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro18517 (p : Pattern) (selected : d194786 p = 0) : d195514 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194762 q = 0) : d96601 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194762, d96601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18511 q selected
    | true =>
      simp only [d194762, d96601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d194763 q = 0) : d96602 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194763, d96602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194763, d96602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194764 q = 0) : d195502 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194764, d195502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194764, d195502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194765 q = 0) : d195503 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194765, d195503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194765, d195503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194766 q = 0) : d195504 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194766, d195504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194766, d195504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d194786 q = 0) : d195514 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194786, d195514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d194786, d195514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18518 (p : Pattern) (selected : d194793 p = 0) : d195570 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194738 q = 0) : d195526 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194738, d195526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18507 q selected
    | true =>
      simp only [d194738, d195526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d194739 q = 0) : d195527 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194739, d195527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194739, d195527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194740 q = 0) : d195528 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194740, d195528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194740, d195528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194741 q = 0) : d195529 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194741, d195529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194741, d195529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d194745 q = 0) : d195533 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194745, d195533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18508 q selected
    | true =>
      simp only [d194745, d195533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d194746 q = 0) : d195534 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194746, d195534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194746, d195534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d194747 q = 0) : d195535 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194747, d195535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d194747, d195535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d194759 q = 0) : d195547 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194759, d195547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18510 q selected
    | true =>
      simp only [d194759, d195547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18503 q selected
  have h9 (q : Pattern) (selected : d194768 q = 0) : d195506 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194768, d195506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18512 q selected
    | true =>
      simp only [d194768, d195506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d194769 q = 0) : d195548 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194769, d195548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d194769, d195548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d194718 q = 0) : d195506 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194718, d195506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18503 q selected
    | true =>
      simp only [d194718, d195506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d194770 q = 0) : d195549 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194770, d195549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d194770, d195549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d194771 q = 0) : d195550 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194771, d195550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d194771, d195550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d194772 q = 0) : d195551 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194772, d195551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d194772, d195551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d194773 q = 0) : d195552 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194773, d195552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194773, d195552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d194776 q = 0) : d195555 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194776, d195555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18514 q selected
    | true =>
      simp only [d194776, d195555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d194777 q = 0) : d195556 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194777, d195556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194777, d195556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d194778 q = 0) : d195557 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194778, d195557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d194778, d195557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d194779 q = 0) : d195558 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194779, d195558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194779, d195558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d194781 q = 0) : d195560 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194781, d195560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18515 q selected
    | true =>
      simp only [d194781, d195560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d194782 q = 0) : d195561 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194782, d195561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194782, d195561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d194783 q = 0) : d195562 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194783, d195562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d194783, d195562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d194785 q = 0) : d195564 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194785, d195564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18516 q selected
    | true =>
      simp only [d194785, d195564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18505 q selected
  have h24 (q : Pattern) (selected : d194787 q = 0) : d195515 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194787, d195515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18517 q selected
    | true =>
      simp only [d194787, d195515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d194788 q = 0) : d195565 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194788, d195565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d194788, d195565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d194727 q = 0) : d195515 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194727, d195515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18505 q selected
    | true =>
      simp only [d194727, d195515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d194789 q = 0) : d195566 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194789, d195566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d194789, d195566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d194790 q = 0) : d195567 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194790, d195567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d194790, d195567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d194791 q = 0) : d195568 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194791, d195568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d194791, d195568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d194792 q = 0) : d195569 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194792, d195569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d194792, d195569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d194793 q = 0) : d195570 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194793, d195570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d194793, d195570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro18519 (p : Pattern) (selected : d194795 p = 0) : d195572 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194718 q = 0) : d195506 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194718, d195506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18503 q selected
    | true =>
      simp only [d194718, d195506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d194719 q = 0) : d195507 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194719, d195507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194719, d195507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194720 q = 0) : d195508 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194720, d195508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194720, d195508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194721 q = 0) : d195509 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194721, d195509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194721, d195509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d194722 q = 0) : d195510 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194722, d195510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194722, d195510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194795 q = 0) : d195572 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194795, d195572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d194795, d195572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18520 (p : Pattern) (selected : d194802 p = 0) : d195579 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194785 q = 0) : d195564 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194785, d195564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18516 q selected
    | true =>
      simp only [d194785, d195564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18505 q selected
  have h2 (q : Pattern) (selected : d194787 q = 0) : d195515 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194787, d195515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18517 q selected
    | true =>
      simp only [d194787, d195515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d194788 q = 0) : d195565 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194788, d195565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d194788, d195565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d194727 q = 0) : d195515 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194727, d195515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18505 q selected
    | true =>
      simp only [d194727, d195515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194789 q = 0) : d195566 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194789, d195566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194789, d195566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d194790 q = 0) : d195567 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194790, d195567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194790, d195567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d194800 q = 0) : d195577 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194800, d195577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194800, d195577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d194801 q = 0) : d195578 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194801, d195578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194801, d195578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d194802 q = 0) : d195579 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194802, d195579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194802, d195579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro18521 (p : Pattern) (selected : d194812 p = 0) : d195589 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194808 q = 0) : d195585 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d194808, d195585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6118 q selected
    | true =>
      simp only [d194808, d195585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15042 q selected
  have h2 (q : Pattern) (selected : d194809 q = 0) : d195586 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d194809, d195586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194809, d195586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194810 q = 0) : d195587 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d194810, d195587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194810, d195587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95295 q = 0) : d96680 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95295, d96680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6119 q selected
    | true =>
      simp only [d95295, d96680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6120 q selected
  have h5 (q : Pattern) (selected : d95296 q = 0) : d96681 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95296, d96681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95296, d96681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95297 q = 0) : d96682 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95297, d96682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95297, d96682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d194811 q = 0) : d195588 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d194811, d195588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194811, d195588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d194812 q = 0) : d195589 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d194812, d195589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d194812, d195589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro18522 (p : Pattern) (selected : d194818 p = 0) : d195595 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194813 q = 0) : d195590 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194813, d195590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18521 q selected
    | true =>
      simp only [d194813, d195590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d194814 q = 0) : d195591 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194814, d195591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194814, d195591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95304 q = 0) : d96689 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95304, d96689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6122 q selected
    | true =>
      simp only [d95304, d96689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95305 q = 0) : d96690 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95305, d96690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95305, d96690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d194815 q = 0) : d195592 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194815, d195592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194815, d195592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194816 q = 0) : d195593 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194816, d195593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d194816, d195593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d194817 q = 0) : d195594 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194817, d195594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d194817, d195594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d194818 q = 0) : d195595 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194818, d195595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d194818, d195595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro18523 (p : Pattern) (selected : d194822 p = 0) : d195599 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95304 q = 0) : d96689 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95304, d96689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6122 q selected
    | true =>
      simp only [d95304, d96689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95305 q = 0) : d96690 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95305, d96690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95305, d96690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194819 q = 0) : d195596 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194819, d195596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194819, d195596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194820 q = 0) : d195597 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194820, d195597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194820, d195597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194821 q = 0) : d195598 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194821, d195598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194821, d195598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d194822 q = 0) : d195599 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194822, d195599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d194822, d195599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18524 (p : Pattern) (selected : d194825 p = 0) : d96688 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95322 q = 0) : d96680 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95322, d96680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6126 q selected
    | true =>
      simp only [d95322, d96680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6127 q selected
  have h2 (q : Pattern) (selected : d95323 q = 0) : d96681 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95323, d96681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95323, d96681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95324 q = 0) : d96682 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95324, d96682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95324, d96682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d194824 q = 0) : d96687 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d194824, d96687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194824, d96687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194825 q = 0) : d96688 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d194825, d96688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194825, d96688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro18525 (p : Pattern) (selected : d194831 p = 0) : d195599 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194826 q = 0) : d96689 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194826, d96689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18524 q selected
    | true =>
      simp only [d194826, d96689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d194827 q = 0) : d96690 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194827, d96690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194827, d96690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194828 q = 0) : d195596 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194828, d195596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194828, d195596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194829 q = 0) : d195597 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194829, d195597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194829, d195597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194830 q = 0) : d195598 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194830, d195598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194830, d195598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d194831 q = 0) : d195599 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194831, d195599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d194831, d195599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18526 (p : Pattern) (selected : d194839 p = 0) : d195607 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194823 q = 0) : d195600 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194823, d195600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18522 q selected
    | true =>
      simp only [d194823, d195600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18523 q selected
  have h2 (q : Pattern) (selected : d194832 q = 0) : d195601 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194832, d195601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18525 q selected
    | true =>
      simp only [d194832, d195601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d194833 q = 0) : d195602 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194833, d195602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d194833, d195602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d194834 q = 0) : d195601 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194834, d195601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18523 q selected
    | true =>
      simp only [d194834, d195601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194835 q = 0) : d195603 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194835, d195603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194835, d195603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d194836 q = 0) : d195604 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194836, d195604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194836, d195604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d194837 q = 0) : d195605 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194837, d195605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194837, d195605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d194838 q = 0) : d195606 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194838, d195606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194838, d195606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d194839 q = 0) : d195607 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194839, d195607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194839, d195607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro18527 (p : Pattern) (selected : d194845 p = 0) : d195613 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194724 q = 0) : d195512 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194724, d195512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194724, d195512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18504 q selected
  have h2 (q : Pattern) (selected : d194725 q = 0) : d195513 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194725, d195513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d194725, d195513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d194733 q = 0) : d195521 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194733, d195521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18504 q selected
    | true =>
      simp only [d194733, d195521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18506 q selected
  have h4 (q : Pattern) (selected : d194734 q = 0) : d195522 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194734, d195522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194734, d195522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194735 q = 0) : d195523 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194735, d195523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194735, d195523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194794 q = 0) : d195571 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194794, d195571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18513 q selected
    | true =>
      simp only [d194794, d195571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18518 q selected
  have h7 (q : Pattern) (selected : d194796 q = 0) : d195573 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194796, d195573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18519 q selected
    | true =>
      simp only [d194796, d195573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d194797 q = 0) : d195574 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194797, d195574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d194797, d195574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d194798 q = 0) : d195575 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194798, d195575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d194798, d195575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d194799 q = 0) : d195576 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194799, d195576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d194799, d195576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d194803 q = 0) : d195580 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194803, d195580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194803, d195580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18520 q selected
  have h12 (q : Pattern) (selected : d194804 q = 0) : d195581 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194804, d195581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d194804, d195581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d194805 q = 0) : d195582 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194805, d195582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d194805, d195582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d194806 q = 0) : d195583 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194806, d195583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d194806, d195583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d194807 q = 0) : d195584 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194807, d195584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d194807, d195584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d194840 q = 0) : d195608 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194840, d195608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194840, d195608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18526 q selected
  have h17 (q : Pattern) (selected : d194841 q = 0) : d195609 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194841, d195609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d194841, d195609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d194842 q = 0) : d195610 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194842, d195610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d194842, d195610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d194843 q = 0) : d195611 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194843, d195611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d194843, d195611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d194844 q = 0) : d195612 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194844, d195612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d194844, d195612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d194845 q = 0) : d195613 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194845, d195613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d194845, d195613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro18528 (p : Pattern) (selected : d194851 p = 0) : d195619 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194846 q = 0) : d195614 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194846, d195614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194846, d195614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18527 q selected
  have h2 (q : Pattern) (selected : d194847 q = 0) : d195615 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194847, d195615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194847, d195615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194848 q = 0) : d195616 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194848, d195616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194848, d195616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d194849 q = 0) : d195617 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194849, d195617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194849, d195617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d194850 q = 0) : d195618 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194850, d195618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194850, d195618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194851 q = 0) : d195619 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194851, d195619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194851, d195619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18529 (p : Pattern) (selected : d194858 p = 0) : d195626 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194854 q = 0) : d195622 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d194854, d195622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6139 q selected
    | true =>
      simp only [d194854, d195622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15049 q selected
  have h2 (q : Pattern) (selected : d194855 q = 0) : d195623 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d194855, d195623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194855, d195623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194856 q = 0) : d195624 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d194856, d195624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194856, d195624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d194857 q = 0) : d195625 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d194857, d195625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194857, d195625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194858 q = 0) : d195626 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d194858, d195626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194858, d195626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro18530 (p : Pattern) (selected : d194864 p = 0) : d195632 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194859 q = 0) : d195627 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194859, d195627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18529 q selected
    | true =>
      simp only [d194859, d195627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d194860 q = 0) : d195628 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194860, d195628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194860, d195628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194861 q = 0) : d195629 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194861, d195629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194861, d195629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194862 q = 0) : d195630 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194862, d195630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194862, d195630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194863 q = 0) : d195631 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194863, d195631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194863, d195631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d194864 q = 0) : d195632 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194864, d195632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194864, d195632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18531 (p : Pattern) (selected : d194870 p = 0) : d195638 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194865 q = 0) : d195633 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194865, d195633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18530 q selected
    | true =>
      simp only [d194865, d195633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d194866 q = 0) : d195634 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194866, d195634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194866, d195634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194867 q = 0) : d195635 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194867, d195635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194867, d195635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194868 q = 0) : d195636 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194868, d195636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194868, d195636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d194869 q = 0) : d195637 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194869, d195637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194869, d195637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194870 q = 0) : d195638 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194870, d195638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194870, d195638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18532 (p : Pattern) (selected : d194873 p = 0) : d195641 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194859 q = 0) : d195627 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194859, d195627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18529 q selected
    | true =>
      simp only [d194859, d195627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d194860 q = 0) : d195628 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194860, d195628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194860, d195628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194861 q = 0) : d195629 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194861, d195629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194861, d195629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194862 q = 0) : d195630 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194862, d195630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194862, d195630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194863 q = 0) : d195631 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194863, d195631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194863, d195631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d194873 q = 0) : d195641 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194873, d195641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d194873, d195641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18533 (p : Pattern) (selected : d194879 p = 0) : d195647 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194865 q = 0) : d195633 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194865, d195633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18530 q selected
    | true =>
      simp only [d194865, d195633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d194866 q = 0) : d195634 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194866, d195634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194866, d195634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194867 q = 0) : d195635 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194867, d195635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194867, d195635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194868 q = 0) : d195636 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194868, d195636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194868, d195636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d194869 q = 0) : d195637 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194869, d195637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194869, d195637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194874 q = 0) : d195642 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194874, d195642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18532 q selected
    | true =>
      simp only [d194874, d195642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d194875 q = 0) : d195643 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194875, d195643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194875, d195643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d194876 q = 0) : d195644 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194876, d195644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d194876, d195644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d194877 q = 0) : d195645 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194877, d195645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194877, d195645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d194878 q = 0) : d195646 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194878, d195646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194878, d195646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d194879 q = 0) : d195647 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194879, d195647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d194879, d195647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro18534 (p : Pattern) (selected : d194884 p = 0) : d195652 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194859 q = 0) : d195627 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194859, d195627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18529 q selected
    | true =>
      simp only [d194859, d195627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d194860 q = 0) : d195628 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194860, d195628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194860, d195628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194861 q = 0) : d195629 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194861, d195629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194861, d195629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194862 q = 0) : d195630 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194862, d195630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194862, d195630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194883 q = 0) : d195651 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194883, d195651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194883, d195651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194884 q = 0) : d195652 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194884, d195652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194884, d195652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18535 (p : Pattern) (selected : d194891 p = 0) : d195659 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194859 q = 0) : d195627 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194859, d195627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18529 q selected
    | true =>
      simp only [d194859, d195627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d194860 q = 0) : d195628 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194860, d195628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194860, d195628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194861 q = 0) : d195629 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194861, d195629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194861, d195629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194889 q = 0) : d195657 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194889, d195657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194889, d195657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d194890 q = 0) : d195658 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194890, d195658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194890, d195658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d194891 q = 0) : d195659 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194891, d195659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194891, d195659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18536 (p : Pattern) (selected : d194899 p = 0) : d195667 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194895 q = 0) : d195663 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d194895, d195663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6154 q selected
    | true =>
      simp only [d194895, d195663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15057 q selected
  have h2 (q : Pattern) (selected : d194896 q = 0) : d195664 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d194896, d195664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194896, d195664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194897 q = 0) : d195665 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d194897, d195665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194897, d195665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d194854 q = 0) : d195622 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d194854, d195622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6139 q selected
    | true =>
      simp only [d194854, d195622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15049 q selected
  have h5 (q : Pattern) (selected : d194855 q = 0) : d195623 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d194855, d195623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194855, d195623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194856 q = 0) : d195624 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d194856, d195624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194856, d195624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d194898 q = 0) : d195666 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d194898, d195666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194898, d195666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d194899 q = 0) : d195667 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d194899, d195667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d194899, d195667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro18537 (p : Pattern) (selected : d194905 p = 0) : d195673 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194900 q = 0) : d195668 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194900, d195668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18536 q selected
    | true =>
      simp only [d194900, d195668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d194901 q = 0) : d195669 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194901, d195669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194901, d195669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194859 q = 0) : d195627 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194859, d195627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18529 q selected
    | true =>
      simp only [d194859, d195627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194860 q = 0) : d195628 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194860, d195628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194860, d195628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d194902 q = 0) : d195670 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194902, d195670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194902, d195670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194903 q = 0) : d195671 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194903, d195671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d194903, d195671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d194904 q = 0) : d195672 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194904, d195672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d194904, d195672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d194905 q = 0) : d195673 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194905, d195673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194905, d195673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro18538 (p : Pattern) (selected : d194911 p = 0) : d195626 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194907 q = 0) : d195622 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d194907, d195622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6159 q selected
    | true =>
      simp only [d194907, d195622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15062 q selected
  have h2 (q : Pattern) (selected : d194908 q = 0) : d195623 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d194908, d195623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194908, d195623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194909 q = 0) : d195624 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d194909, d195624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194909, d195624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d194910 q = 0) : d195625 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d194910, d195625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194910, d195625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194911 q = 0) : d195626 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d194911, d195626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194911, d195626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro18539 (p : Pattern) (selected : d194917 p = 0) : d195632 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194912 q = 0) : d195627 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194912, d195627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18538 q selected
    | true =>
      simp only [d194912, d195627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d194913 q = 0) : d195628 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194913, d195628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194913, d195628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194914 q = 0) : d195629 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194914, d195629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194914, d195629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194915 q = 0) : d195630 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194915, d195630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194915, d195630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194916 q = 0) : d195631 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194916, d195631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194916, d195631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d194917 q = 0) : d195632 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194917, d195632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194917, d195632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18540 (p : Pattern) (selected : d194924 p = 0) : d195680 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194885 q = 0) : d195653 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194885, d195653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18534 q selected
    | true =>
      simp only [d194885, d195653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d194886 q = 0) : d195654 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194886, d195654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194886, d195654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194887 q = 0) : d195655 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194887, d195655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194887, d195655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194888 q = 0) : d195656 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194888, d195656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194888, d195656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d194892 q = 0) : d195660 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194892, d195660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18535 q selected
    | true =>
      simp only [d194892, d195660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d194893 q = 0) : d195661 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194893, d195661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194893, d195661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d194894 q = 0) : d195662 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194894, d195662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d194894, d195662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d194906 q = 0) : d195674 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194906, d195674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18537 q selected
    | true =>
      simp only [d194906, d195674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18530 q selected
  have h9 (q : Pattern) (selected : d194918 q = 0) : d195633 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194918, d195633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18539 q selected
    | true =>
      simp only [d194918, d195633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d194919 q = 0) : d195675 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194919, d195675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d194919, d195675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d194865 q = 0) : d195633 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194865, d195633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18530 q selected
    | true =>
      simp only [d194865, d195633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d194920 q = 0) : d195676 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194920, d195676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d194920, d195676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d194921 q = 0) : d195677 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194921, d195677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d194921, d195677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d194922 q = 0) : d195678 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194922, d195678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d194922, d195678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d194923 q = 0) : d195679 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194923, d195679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194923, d195679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d194924 q = 0) : d195680 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194924, d195680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194924, d195680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro18541 (p : Pattern) (selected : d194925 p = 0) : d195681 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194859 q = 0) : d195627 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194859, d195627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18529 q selected
    | true =>
      simp only [d194859, d195627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d194860 q = 0) : d195628 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194860, d195628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194860, d195628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194861 q = 0) : d195629 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194861, d195629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194861, d195629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194862 q = 0) : d195630 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194862, d195630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194862, d195630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194883 q = 0) : d195651 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194883, d195651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194883, d195651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194925 q = 0) : d195681 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194925, d195681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d194925, d195681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18542 (p : Pattern) (selected : d194930 p = 0) : d195686 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194859 q = 0) : d195627 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194859, d195627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18529 q selected
    | true =>
      simp only [d194859, d195627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d194860 q = 0) : d195628 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194860, d195628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194860, d195628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194861 q = 0) : d195629 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194861, d195629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194861, d195629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194889 q = 0) : d195657 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194889, d195657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194889, d195657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d194890 q = 0) : d195658 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194890, d195658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194890, d195658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d194930 q = 0) : d195686 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194930, d195686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d194930, d195686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18543 (p : Pattern) (selected : d194934 p = 0) : d195690 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194900 q = 0) : d195668 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194900, d195668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18536 q selected
    | true =>
      simp only [d194900, d195668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d194901 q = 0) : d195669 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194901, d195669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194901, d195669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194859 q = 0) : d195627 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194859, d195627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18529 q selected
    | true =>
      simp only [d194859, d195627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194860 q = 0) : d195628 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194860, d195628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194860, d195628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d194902 q = 0) : d195670 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194902, d195670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194902, d195670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194903 q = 0) : d195671 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194903, d195671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d194903, d195671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d194904 q = 0) : d195672 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194904, d195672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d194904, d195672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d194934 q = 0) : d195690 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194934, d195690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d194934, d195690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro18544 (p : Pattern) (selected : d194936 p = 0) : d195641 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194912 q = 0) : d195627 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194912, d195627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18538 q selected
    | true =>
      simp only [d194912, d195627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d194913 q = 0) : d195628 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194913, d195628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194913, d195628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194914 q = 0) : d195629 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194914, d195629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194914, d195629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194915 q = 0) : d195630 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194915, d195630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194915, d195630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194916 q = 0) : d195631 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194916, d195631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194916, d195631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d194936 q = 0) : d195641 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194936, d195641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d194936, d195641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18545 (p : Pattern) (selected : d194943 p = 0) : d195697 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194885 q = 0) : d195653 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194885, d195653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18534 q selected
    | true =>
      simp only [d194885, d195653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d194886 q = 0) : d195654 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194886, d195654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194886, d195654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194887 q = 0) : d195655 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194887, d195655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194887, d195655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194888 q = 0) : d195656 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194888, d195656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194888, d195656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d194892 q = 0) : d195660 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194892, d195660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18535 q selected
    | true =>
      simp only [d194892, d195660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d194893 q = 0) : d195661 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194893, d195661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194893, d195661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d194894 q = 0) : d195662 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194894, d195662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d194894, d195662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d194906 q = 0) : d195674 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194906, d195674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18537 q selected
    | true =>
      simp only [d194906, d195674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18530 q selected
  have h9 (q : Pattern) (selected : d194918 q = 0) : d195633 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194918, d195633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18539 q selected
    | true =>
      simp only [d194918, d195633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d194919 q = 0) : d195675 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194919, d195675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d194919, d195675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d194865 q = 0) : d195633 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194865, d195633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18530 q selected
    | true =>
      simp only [d194865, d195633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d194920 q = 0) : d195676 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194920, d195676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d194920, d195676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d194921 q = 0) : d195677 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194921, d195677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d194921, d195677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d194922 q = 0) : d195678 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194922, d195678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d194922, d195678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d194923 q = 0) : d195679 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194923, d195679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194923, d195679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d194926 q = 0) : d195682 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194926, d195682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18541 q selected
    | true =>
      simp only [d194926, d195682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d194927 q = 0) : d195683 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194927, d195683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194927, d195683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d194928 q = 0) : d195684 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194928, d195684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d194928, d195684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d194929 q = 0) : d195685 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194929, d195685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194929, d195685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d194931 q = 0) : d195687 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194931, d195687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18542 q selected
    | true =>
      simp only [d194931, d195687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d194932 q = 0) : d195688 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194932, d195688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194932, d195688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d194933 q = 0) : d195689 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194933, d195689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d194933, d195689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d194935 q = 0) : d195691 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194935, d195691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18543 q selected
    | true =>
      simp only [d194935, d195691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18532 q selected
  have h24 (q : Pattern) (selected : d194937 q = 0) : d195642 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194937, d195642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18544 q selected
    | true =>
      simp only [d194937, d195642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d194938 q = 0) : d195692 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194938, d195692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d194938, d195692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d194874 q = 0) : d195642 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194874, d195642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18532 q selected
    | true =>
      simp only [d194874, d195642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d194939 q = 0) : d195693 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194939, d195693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d194939, d195693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d194940 q = 0) : d195694 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194940, d195694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d194940, d195694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d194941 q = 0) : d195695 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194941, d195695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d194941, d195695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d194942 q = 0) : d195696 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194942, d195696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d194942, d195696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d194943 q = 0) : d195697 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194943, d195697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d194943, d195697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro18546 (p : Pattern) (selected : d194945 p = 0) : d195699 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194865 q = 0) : d195633 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194865, d195633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18530 q selected
    | true =>
      simp only [d194865, d195633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d194866 q = 0) : d195634 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194866, d195634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194866, d195634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194867 q = 0) : d195635 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194867, d195635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194867, d195635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194868 q = 0) : d195636 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194868, d195636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194868, d195636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d194869 q = 0) : d195637 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194869, d195637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194869, d195637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194945 q = 0) : d195699 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194945, d195699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d194945, d195699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18547 (p : Pattern) (selected : d194952 p = 0) : d195706 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194935 q = 0) : d195691 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194935, d195691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18543 q selected
    | true =>
      simp only [d194935, d195691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18532 q selected
  have h2 (q : Pattern) (selected : d194937 q = 0) : d195642 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194937, d195642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18544 q selected
    | true =>
      simp only [d194937, d195642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d194938 q = 0) : d195692 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194938, d195692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d194938, d195692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d194874 q = 0) : d195642 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194874, d195642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18532 q selected
    | true =>
      simp only [d194874, d195642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194939 q = 0) : d195693 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194939, d195693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194939, d195693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d194940 q = 0) : d195694 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194940, d195694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194940, d195694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d194950 q = 0) : d195704 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194950, d195704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194950, d195704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d194951 q = 0) : d195705 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194951, d195705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194951, d195705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d194952 q = 0) : d195706 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194952, d195706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194952, d195706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro18548 (p : Pattern) (selected : d194965 p = 0) : d195719 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194958 q = 0) : d195712 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d194958, d195712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6182 q selected
    | true =>
      simp only [d194958, d195712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15077 q selected
  have h2 (q : Pattern) (selected : d194959 q = 0) : d195713 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d194959, d195713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194959, d195713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194960 q = 0) : d195714 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d194960, d195714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194960, d195714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d194961 q = 0) : d195715 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d194961, d195715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6183 q selected
    | true =>
      simp only [d194961, d195715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15076 q selected
  have h5 (q : Pattern) (selected : d194962 q = 0) : d195716 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d194962, d195716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194962, d195716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194963 q = 0) : d195717 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d194963, d195717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194963, d195717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d194964 q = 0) : d195718 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d194964, d195718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194964, d195718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d194965 q = 0) : d195719 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d194965, d195719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d194965, d195719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro18549 (p : Pattern) (selected : d194969 p = 0) : d195723 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194961 q = 0) : d195715 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d194961, d195715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6183 q selected
    | true =>
      simp only [d194961, d195715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15076 q selected
  have h2 (q : Pattern) (selected : d194962 q = 0) : d195716 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d194962, d195716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194962, d195716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194963 q = 0) : d195717 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d194963, d195717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194963, d195717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d194968 q = 0) : d195722 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d194968, d195722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194968, d195722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194969 q = 0) : d195723 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d194969, d195723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194969, d195723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro18550 (p : Pattern) (selected : d194975 p = 0) : d195729 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194966 q = 0) : d195720 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194966, d195720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18548 q selected
    | true =>
      simp only [d194966, d195720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d194967 q = 0) : d195721 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194967, d195721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194967, d195721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194970 q = 0) : d195724 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194970, d195724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18549 q selected
    | true =>
      simp only [d194970, d195724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194971 q = 0) : d195725 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194971, d195725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194971, d195725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d194972 q = 0) : d195726 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194972, d195726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194972, d195726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194973 q = 0) : d195727 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194973, d195727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d194973, d195727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d194974 q = 0) : d195728 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194974, d195728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d194974, d195728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d194975 q = 0) : d195729 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194975, d195729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d194975, d195729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro18551 (p : Pattern) (selected : d194979 p = 0) : d195733 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194970 q = 0) : d195724 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194970, d195724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18549 q selected
    | true =>
      simp only [d194970, d195724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d194971 q = 0) : d195725 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194971, d195725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194971, d195725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194976 q = 0) : d195730 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194976, d195730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194976, d195730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194977 q = 0) : d195731 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194977, d195731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194977, d195731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194978 q = 0) : d195732 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194978, d195732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194978, d195732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d194979 q = 0) : d195733 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194979, d195733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d194979, d195733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18552 (p : Pattern) (selected : d194985 p = 0) : d195723 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194981 q = 0) : d195715 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d194981, d195715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6191 q selected
    | true =>
      simp only [d194981, d195715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15082 q selected
  have h2 (q : Pattern) (selected : d194982 q = 0) : d195716 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d194982, d195716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194982, d195716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194983 q = 0) : d195717 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d194983, d195717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194983, d195717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d194984 q = 0) : d195722 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d194984, d195722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194984, d195722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194985 q = 0) : d195723 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d194985, d195723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194985, d195723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro18553 (p : Pattern) (selected : d194991 p = 0) : d195733 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194986 q = 0) : d195724 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194986, d195724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18552 q selected
    | true =>
      simp only [d194986, d195724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d194987 q = 0) : d195725 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194987, d195725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194987, d195725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194988 q = 0) : d195730 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194988, d195730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194988, d195730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194989 q = 0) : d195731 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194989, d195731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194989, d195731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194990 q = 0) : d195732 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194990, d195732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194990, d195732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d194991 q = 0) : d195733 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194991, d195733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d194991, d195733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18554 (p : Pattern) (selected : d194999 p = 0) : d195741 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194980 q = 0) : d195734 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194980, d195734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18550 q selected
    | true =>
      simp only [d194980, d195734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18551 q selected
  have h2 (q : Pattern) (selected : d194992 q = 0) : d195735 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194992, d195735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18553 q selected
    | true =>
      simp only [d194992, d195735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d194993 q = 0) : d195736 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194993, d195736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d194993, d195736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d194994 q = 0) : d195735 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194994, d195735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18551 q selected
    | true =>
      simp only [d194994, d195735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194995 q = 0) : d195737 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194995, d195737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194995, d195737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d194996 q = 0) : d195738 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194996, d195738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194996, d195738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d194997 q = 0) : d195739 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194997, d195739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194997, d195739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d194998 q = 0) : d195740 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194998, d195740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194998, d195740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d194999 q = 0) : d195741 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194999, d195741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194999, d195741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro18555 (p : Pattern) (selected : d195005 p = 0) : d195747 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d194871 q = 0) : d195639 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194871, d195639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194871, d195639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18531 q selected
  have h2 (q : Pattern) (selected : d194872 q = 0) : d195640 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194872, d195640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d194872, d195640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d194880 q = 0) : d195648 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194880, d195648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18531 q selected
    | true =>
      simp only [d194880, d195648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18533 q selected
  have h4 (q : Pattern) (selected : d194881 q = 0) : d195649 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194881, d195649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194881, d195649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194882 q = 0) : d195650 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194882, d195650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194882, d195650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194944 q = 0) : d195698 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194944, d195698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18540 q selected
    | true =>
      simp only [d194944, d195698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18545 q selected
  have h7 (q : Pattern) (selected : d194946 q = 0) : d195700 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194946, d195700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18546 q selected
    | true =>
      simp only [d194946, d195700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d194947 q = 0) : d195701 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194947, d195701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d194947, d195701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d194948 q = 0) : d195702 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194948, d195702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d194948, d195702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d194949 q = 0) : d195703 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194949, d195703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d194949, d195703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d194953 q = 0) : d195707 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194953, d195707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194953, d195707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18547 q selected
  have h12 (q : Pattern) (selected : d194954 q = 0) : d195708 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194954, d195708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d194954, d195708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d194955 q = 0) : d195709 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194955, d195709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d194955, d195709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d194956 q = 0) : d195710 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194956, d195710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d194956, d195710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d194957 q = 0) : d195711 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194957, d195711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d194957, d195711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d195000 q = 0) : d195742 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195000, d195742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195000, d195742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18554 q selected
  have h17 (q : Pattern) (selected : d195001 q = 0) : d195743 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195001, d195743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d195001, d195743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d195002 q = 0) : d195744 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195002, d195744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d195002, d195744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d195003 q = 0) : d195745 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195003, d195745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d195003, d195745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d195004 q = 0) : d195746 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d195004, d195746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d195004, d195746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d195005 q = 0) : d195747 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d195005, d195747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d195005, d195747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro18556 (p : Pattern) (selected : d195011 p = 0) : d195753 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195006 q = 0) : d195748 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d195006, d195748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195006, d195748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18555 q selected
  have h2 (q : Pattern) (selected : d195007 q = 0) : d195749 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d195007, d195749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195007, d195749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195008 q = 0) : d195750 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d195008, d195750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195008, d195750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d195009 q = 0) : d195751 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d195009, d195751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195009, d195751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d195010 q = 0) : d195752 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d195010, d195752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195010, d195752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195011 q = 0) : d195753 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d195011, d195753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195011, d195753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18557 (p : Pattern) (selected : d195019 p = 0) : d195761 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195015 q = 0) : d195757 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195015, d195757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6205 q selected
    | true =>
      simp only [d195015, d195757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15090 q selected
  have h2 (q : Pattern) (selected : d195016 q = 0) : d195758 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195016, d195758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195016, d195758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195017 q = 0) : d195759 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195017, d195759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195017, d195759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d195018 q = 0) : d195760 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d195018, d195760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195018, d195760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195019 q = 0) : d195761 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d195019, d195761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195019, d195761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro18558 (p : Pattern) (selected : d195025 p = 0) : d195767 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195020 q = 0) : d195762 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195020, d195762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18557 q selected
    | true =>
      simp only [d195020, d195762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195021 q = 0) : d195763 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195021, d195763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195021, d195763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195022 q = 0) : d195764 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195022, d195764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195022, d195764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195023 q = 0) : d195765 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195023, d195765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195023, d195765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195024 q = 0) : d195766 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195024, d195766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195024, d195766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195025 q = 0) : d195767 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195025, d195767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195025, d195767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18559 (p : Pattern) (selected : d195031 p = 0) : d195773 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195026 q = 0) : d195768 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195026, d195768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18558 q selected
    | true =>
      simp only [d195026, d195768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195027 q = 0) : d195769 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195027, d195769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195027, d195769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195028 q = 0) : d195770 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195028, d195770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195028, d195770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195029 q = 0) : d195771 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195029, d195771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195029, d195771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d195030 q = 0) : d195772 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195030, d195772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195030, d195772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195031 q = 0) : d195773 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195031, d195773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195031, d195773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18560 (p : Pattern) (selected : d195034 p = 0) : d195776 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195020 q = 0) : d195762 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195020, d195762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18557 q selected
    | true =>
      simp only [d195020, d195762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195021 q = 0) : d195763 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195021, d195763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195021, d195763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195022 q = 0) : d195764 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195022, d195764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195022, d195764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195023 q = 0) : d195765 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195023, d195765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195023, d195765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195024 q = 0) : d195766 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195024, d195766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195024, d195766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195034 q = 0) : d195776 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195034, d195776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195034, d195776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18561 (p : Pattern) (selected : d195040 p = 0) : d195782 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195026 q = 0) : d195768 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195026, d195768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18558 q selected
    | true =>
      simp only [d195026, d195768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195027 q = 0) : d195769 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195027, d195769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195027, d195769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195028 q = 0) : d195770 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195028, d195770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195028, d195770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195029 q = 0) : d195771 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195029, d195771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195029, d195771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d195030 q = 0) : d195772 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195030, d195772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195030, d195772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195035 q = 0) : d195777 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195035, d195777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18560 q selected
    | true =>
      simp only [d195035, d195777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d195036 q = 0) : d195778 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195036, d195778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195036, d195778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d195037 q = 0) : d195779 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195037, d195779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d195037, d195779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d195038 q = 0) : d195780 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195038, d195780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195038, d195780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d195039 q = 0) : d195781 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195039, d195781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195039, d195781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d195040 q = 0) : d195782 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195040, d195782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195040, d195782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro18562 (p : Pattern) (selected : d195045 p = 0) : d195787 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195020 q = 0) : d195762 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195020, d195762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18557 q selected
    | true =>
      simp only [d195020, d195762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195021 q = 0) : d195763 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195021, d195763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195021, d195763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195022 q = 0) : d195764 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195022, d195764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195022, d195764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195023 q = 0) : d195765 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195023, d195765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195023, d195765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195044 q = 0) : d195786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195044, d195786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195044, d195786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195045 q = 0) : d195787 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195045, d195787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195045, d195787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18563 (p : Pattern) (selected : d195052 p = 0) : d195794 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195020 q = 0) : d195762 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195020, d195762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18557 q selected
    | true =>
      simp only [d195020, d195762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195021 q = 0) : d195763 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195021, d195763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195021, d195763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195022 q = 0) : d195764 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195022, d195764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195022, d195764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195050 q = 0) : d195792 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195050, d195792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195050, d195792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d195051 q = 0) : d195793 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195051, d195793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195051, d195793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195052 q = 0) : d195794 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195052, d195794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195052, d195794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18564 (p : Pattern) (selected : d195060 p = 0) : d195802 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195056 q = 0) : d195798 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195056, d195798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6220 q selected
    | true =>
      simp only [d195056, d195798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15098 q selected
  have h2 (q : Pattern) (selected : d195057 q = 0) : d195799 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195057, d195799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195057, d195799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195058 q = 0) : d195800 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195058, d195800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195058, d195800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d195015 q = 0) : d195757 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195015, d195757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6205 q selected
    | true =>
      simp only [d195015, d195757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15090 q selected
  have h5 (q : Pattern) (selected : d195016 q = 0) : d195758 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195016, d195758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195016, d195758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195017 q = 0) : d195759 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195017, d195759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195017, d195759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d195059 q = 0) : d195801 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d195059, d195801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195059, d195801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d195060 q = 0) : d195802 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d195060, d195802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d195060, d195802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro18565 (p : Pattern) (selected : d195066 p = 0) : d195808 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195061 q = 0) : d195803 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195061, d195803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18564 q selected
    | true =>
      simp only [d195061, d195803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195062 q = 0) : d195804 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195062, d195804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195062, d195804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195020 q = 0) : d195762 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195020, d195762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18557 q selected
    | true =>
      simp only [d195020, d195762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195021 q = 0) : d195763 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195021, d195763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195021, d195763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d195063 q = 0) : d195805 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195063, d195805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195063, d195805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195064 q = 0) : d195806 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195064, d195806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195064, d195806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d195065 q = 0) : d195807 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195065, d195807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d195065, d195807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d195066 q = 0) : d195808 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195066, d195808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195066, d195808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro18566 (p : Pattern) (selected : d195072 p = 0) : d195761 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195068 q = 0) : d195757 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195068, d195757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6225 q selected
    | true =>
      simp only [d195068, d195757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15103 q selected
  have h2 (q : Pattern) (selected : d195069 q = 0) : d195758 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195069, d195758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195069, d195758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195070 q = 0) : d195759 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195070, d195759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195070, d195759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d195071 q = 0) : d195760 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d195071, d195760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195071, d195760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195072 q = 0) : d195761 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d195072, d195761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195072, d195761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro18567 (p : Pattern) (selected : d195078 p = 0) : d195767 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195073 q = 0) : d195762 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195073, d195762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18566 q selected
    | true =>
      simp only [d195073, d195762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195074 q = 0) : d195763 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195074, d195763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195074, d195763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195075 q = 0) : d195764 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195075, d195764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195075, d195764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195076 q = 0) : d195765 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195076, d195765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195076, d195765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195077 q = 0) : d195766 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195077, d195766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195077, d195766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195078 q = 0) : d195767 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195078, d195767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195078, d195767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18568 (p : Pattern) (selected : d195085 p = 0) : d195815 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195046 q = 0) : d195788 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195046, d195788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18562 q selected
    | true =>
      simp only [d195046, d195788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195047 q = 0) : d195789 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195047, d195789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195047, d195789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195048 q = 0) : d195790 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195048, d195790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195048, d195790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195049 q = 0) : d195791 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195049, d195791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195049, d195791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d195053 q = 0) : d195795 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195053, d195795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18563 q selected
    | true =>
      simp only [d195053, d195795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195054 q = 0) : d195796 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195054, d195796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195054, d195796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d195055 q = 0) : d195797 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195055, d195797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d195055, d195797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d195067 q = 0) : d195809 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195067, d195809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18565 q selected
    | true =>
      simp only [d195067, d195809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18558 q selected
  have h9 (q : Pattern) (selected : d195079 q = 0) : d195768 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195079, d195768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18567 q selected
    | true =>
      simp only [d195079, d195768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d195080 q = 0) : d195810 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195080, d195810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d195080, d195810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d195026 q = 0) : d195768 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195026, d195768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18558 q selected
    | true =>
      simp only [d195026, d195768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d195081 q = 0) : d195811 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195081, d195811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d195081, d195811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d195082 q = 0) : d195812 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195082, d195812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d195082, d195812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d195083 q = 0) : d195813 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195083, d195813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d195083, d195813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d195084 q = 0) : d195814 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195084, d195814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195084, d195814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d195085 q = 0) : d195815 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195085, d195815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195085, d195815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro18569 (p : Pattern) (selected : d195086 p = 0) : d195816 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195020 q = 0) : d195762 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195020, d195762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18557 q selected
    | true =>
      simp only [d195020, d195762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195021 q = 0) : d195763 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195021, d195763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195021, d195763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195022 q = 0) : d195764 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195022, d195764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195022, d195764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195023 q = 0) : d195765 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195023, d195765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195023, d195765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195044 q = 0) : d195786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195044, d195786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195044, d195786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195086 q = 0) : d195816 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195086, d195816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195086, d195816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18570 (p : Pattern) (selected : d195091 p = 0) : d195821 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195020 q = 0) : d195762 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195020, d195762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18557 q selected
    | true =>
      simp only [d195020, d195762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195021 q = 0) : d195763 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195021, d195763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195021, d195763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195022 q = 0) : d195764 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195022, d195764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195022, d195764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195050 q = 0) : d195792 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195050, d195792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195050, d195792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d195051 q = 0) : d195793 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195051, d195793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195051, d195793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195091 q = 0) : d195821 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195091, d195821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195091, d195821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18571 (p : Pattern) (selected : d195095 p = 0) : d195825 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195061 q = 0) : d195803 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195061, d195803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18564 q selected
    | true =>
      simp only [d195061, d195803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195062 q = 0) : d195804 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195062, d195804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195062, d195804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195020 q = 0) : d195762 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195020, d195762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18557 q selected
    | true =>
      simp only [d195020, d195762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195021 q = 0) : d195763 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195021, d195763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195021, d195763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d195063 q = 0) : d195805 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195063, d195805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195063, d195805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195064 q = 0) : d195806 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195064, d195806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195064, d195806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d195065 q = 0) : d195807 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195065, d195807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d195065, d195807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d195095 q = 0) : d195825 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195095, d195825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d195095, d195825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro18572 (p : Pattern) (selected : d195097 p = 0) : d195776 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195073 q = 0) : d195762 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195073, d195762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18566 q selected
    | true =>
      simp only [d195073, d195762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195074 q = 0) : d195763 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195074, d195763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195074, d195763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195075 q = 0) : d195764 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195075, d195764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195075, d195764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195076 q = 0) : d195765 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195076, d195765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195076, d195765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195077 q = 0) : d195766 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195077, d195766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195077, d195766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195097 q = 0) : d195776 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195097, d195776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195097, d195776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18573 (p : Pattern) (selected : d195104 p = 0) : d195832 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195046 q = 0) : d195788 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195046, d195788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18562 q selected
    | true =>
      simp only [d195046, d195788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195047 q = 0) : d195789 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195047, d195789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195047, d195789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195048 q = 0) : d195790 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195048, d195790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195048, d195790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195049 q = 0) : d195791 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195049, d195791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195049, d195791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d195053 q = 0) : d195795 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195053, d195795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18563 q selected
    | true =>
      simp only [d195053, d195795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195054 q = 0) : d195796 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195054, d195796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195054, d195796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d195055 q = 0) : d195797 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195055, d195797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d195055, d195797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d195067 q = 0) : d195809 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195067, d195809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18565 q selected
    | true =>
      simp only [d195067, d195809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18558 q selected
  have h9 (q : Pattern) (selected : d195079 q = 0) : d195768 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195079, d195768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18567 q selected
    | true =>
      simp only [d195079, d195768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d195080 q = 0) : d195810 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195080, d195810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d195080, d195810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d195026 q = 0) : d195768 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195026, d195768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18558 q selected
    | true =>
      simp only [d195026, d195768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d195081 q = 0) : d195811 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195081, d195811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d195081, d195811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d195082 q = 0) : d195812 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195082, d195812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d195082, d195812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d195083 q = 0) : d195813 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195083, d195813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d195083, d195813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d195084 q = 0) : d195814 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195084, d195814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195084, d195814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d195087 q = 0) : d195817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195087, d195817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18569 q selected
    | true =>
      simp only [d195087, d195817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d195088 q = 0) : d195818 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195088, d195818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195088, d195818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d195089 q = 0) : d195819 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195089, d195819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d195089, d195819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d195090 q = 0) : d195820 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195090, d195820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195090, d195820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d195092 q = 0) : d195822 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195092, d195822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18570 q selected
    | true =>
      simp only [d195092, d195822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d195093 q = 0) : d195823 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195093, d195823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195093, d195823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d195094 q = 0) : d195824 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195094, d195824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d195094, d195824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d195096 q = 0) : d195826 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195096, d195826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18571 q selected
    | true =>
      simp only [d195096, d195826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18560 q selected
  have h24 (q : Pattern) (selected : d195098 q = 0) : d195777 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195098, d195777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18572 q selected
    | true =>
      simp only [d195098, d195777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d195099 q = 0) : d195827 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195099, d195827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d195099, d195827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d195035 q = 0) : d195777 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195035, d195777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18560 q selected
    | true =>
      simp only [d195035, d195777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d195100 q = 0) : d195828 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195100, d195828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d195100, d195828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d195101 q = 0) : d195829 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195101, d195829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d195101, d195829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d195102 q = 0) : d195830 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195102, d195830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d195102, d195830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d195103 q = 0) : d195831 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195103, d195831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d195103, d195831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d195104 q = 0) : d195832 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195104, d195832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d195104, d195832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro18574 (p : Pattern) (selected : d195106 p = 0) : d195834 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195026 q = 0) : d195768 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195026, d195768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18558 q selected
    | true =>
      simp only [d195026, d195768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195027 q = 0) : d195769 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195027, d195769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195027, d195769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195028 q = 0) : d195770 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195028, d195770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195028, d195770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195029 q = 0) : d195771 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195029, d195771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195029, d195771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d195030 q = 0) : d195772 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195030, d195772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195030, d195772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195106 q = 0) : d195834 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195106, d195834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195106, d195834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18575 (p : Pattern) (selected : d195113 p = 0) : d195841 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195096 q = 0) : d195826 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195096, d195826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18571 q selected
    | true =>
      simp only [d195096, d195826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18560 q selected
  have h2 (q : Pattern) (selected : d195098 q = 0) : d195777 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195098, d195777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18572 q selected
    | true =>
      simp only [d195098, d195777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d195099 q = 0) : d195827 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195099, d195827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195099, d195827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d195035 q = 0) : d195777 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195035, d195777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18560 q selected
    | true =>
      simp only [d195035, d195777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195100 q = 0) : d195828 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195100, d195828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195100, d195828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195101 q = 0) : d195829 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195101, d195829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195101, d195829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d195111 q = 0) : d195839 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195111, d195839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195111, d195839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d195112 q = 0) : d195840 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195112, d195840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195112, d195840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d195113 q = 0) : d195841 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195113, d195841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195113, d195841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro18576 (p : Pattern) (selected : d195126 p = 0) : d195854 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195119 q = 0) : d195847 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195119, d195847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6248 q selected
    | true =>
      simp only [d195119, d195847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15118 q selected
  have h2 (q : Pattern) (selected : d195120 q = 0) : d195848 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195120, d195848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195120, d195848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195121 q = 0) : d195849 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195121, d195849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195121, d195849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d195122 q = 0) : d195850 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195122, d195850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6249 q selected
    | true =>
      simp only [d195122, d195850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15117 q selected
  have h5 (q : Pattern) (selected : d195123 q = 0) : d195851 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195123, d195851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195123, d195851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195124 q = 0) : d195852 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195124, d195852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195124, d195852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d195125 q = 0) : d195853 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d195125, d195853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195125, d195853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d195126 q = 0) : d195854 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d195126, d195854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d195126, d195854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro18577 (p : Pattern) (selected : d195130 p = 0) : d195858 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195122 q = 0) : d195850 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195122, d195850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6249 q selected
    | true =>
      simp only [d195122, d195850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15117 q selected
  have h2 (q : Pattern) (selected : d195123 q = 0) : d195851 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195123, d195851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195123, d195851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195124 q = 0) : d195852 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195124, d195852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195124, d195852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d195129 q = 0) : d195857 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d195129, d195857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195129, d195857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195130 q = 0) : d195858 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d195130, d195858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195130, d195858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro18578 (p : Pattern) (selected : d195136 p = 0) : d195864 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195127 q = 0) : d195855 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195127, d195855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18576 q selected
    | true =>
      simp only [d195127, d195855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195128 q = 0) : d195856 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195128, d195856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195128, d195856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195131 q = 0) : d195859 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195131, d195859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18577 q selected
    | true =>
      simp only [d195131, d195859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195132 q = 0) : d195860 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195132, d195860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195132, d195860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d195133 q = 0) : d195861 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195133, d195861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195133, d195861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195134 q = 0) : d195862 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195134, d195862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195134, d195862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d195135 q = 0) : d195863 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195135, d195863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d195135, d195863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d195136 q = 0) : d195864 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195136, d195864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d195136, d195864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro18579 (p : Pattern) (selected : d195140 p = 0) : d195868 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195131 q = 0) : d195859 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195131, d195859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18577 q selected
    | true =>
      simp only [d195131, d195859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195132 q = 0) : d195860 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195132, d195860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195132, d195860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195137 q = 0) : d195865 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195137, d195865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195137, d195865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195138 q = 0) : d195866 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195138, d195866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195138, d195866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195139 q = 0) : d195867 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195139, d195867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195139, d195867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195140 q = 0) : d195868 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195140, d195868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195140, d195868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18580 (p : Pattern) (selected : d195146 p = 0) : d195858 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195142 q = 0) : d195850 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195142, d195850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6257 q selected
    | true =>
      simp only [d195142, d195850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15123 q selected
  have h2 (q : Pattern) (selected : d195143 q = 0) : d195851 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195143, d195851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195143, d195851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195144 q = 0) : d195852 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195144, d195852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195144, d195852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d195145 q = 0) : d195857 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d195145, d195857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195145, d195857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195146 q = 0) : d195858 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d195146, d195858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195146, d195858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro18581 (p : Pattern) (selected : d195152 p = 0) : d195868 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195147 q = 0) : d195859 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195147, d195859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18580 q selected
    | true =>
      simp only [d195147, d195859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195148 q = 0) : d195860 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195148, d195860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195148, d195860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195149 q = 0) : d195865 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195149, d195865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195149, d195865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195150 q = 0) : d195866 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195150, d195866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195150, d195866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195151 q = 0) : d195867 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195151, d195867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195151, d195867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195152 q = 0) : d195868 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195152, d195868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195152, d195868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18582 (p : Pattern) (selected : d195160 p = 0) : d195876 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195141 q = 0) : d195869 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195141, d195869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18578 q selected
    | true =>
      simp only [d195141, d195869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18579 q selected
  have h2 (q : Pattern) (selected : d195153 q = 0) : d195870 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195153, d195870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18581 q selected
    | true =>
      simp only [d195153, d195870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d195154 q = 0) : d195871 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195154, d195871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195154, d195871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d195155 q = 0) : d195870 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195155, d195870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18579 q selected
    | true =>
      simp only [d195155, d195870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195156 q = 0) : d195872 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195156, d195872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195156, d195872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195157 q = 0) : d195873 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195157, d195873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195157, d195873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d195158 q = 0) : d195874 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195158, d195874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195158, d195874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d195159 q = 0) : d195875 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195159, d195875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195159, d195875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d195160 q = 0) : d195876 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195160, d195876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195160, d195876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro18583 (p : Pattern) (selected : d195166 p = 0) : d195882 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195032 q = 0) : d195774 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195032, d195774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195032, d195774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18559 q selected
  have h2 (q : Pattern) (selected : d195033 q = 0) : d195775 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195033, d195775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195033, d195775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d195041 q = 0) : d195783 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195041, d195783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18559 q selected
    | true =>
      simp only [d195041, d195783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18561 q selected
  have h4 (q : Pattern) (selected : d195042 q = 0) : d195784 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195042, d195784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195042, d195784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195043 q = 0) : d195785 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195043, d195785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195043, d195785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195105 q = 0) : d195833 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195105, d195833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18568 q selected
    | true =>
      simp only [d195105, d195833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18573 q selected
  have h7 (q : Pattern) (selected : d195107 q = 0) : d195835 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195107, d195835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18574 q selected
    | true =>
      simp only [d195107, d195835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d195108 q = 0) : d195836 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195108, d195836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d195108, d195836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d195109 q = 0) : d195837 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195109, d195837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d195109, d195837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d195110 q = 0) : d195838 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195110, d195838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195110, d195838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d195114 q = 0) : d195842 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195114, d195842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195114, d195842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18575 q selected
  have h12 (q : Pattern) (selected : d195115 q = 0) : d195843 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195115, d195843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d195115, d195843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d195116 q = 0) : d195844 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195116, d195844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d195116, d195844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d195117 q = 0) : d195845 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195117, d195845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d195117, d195845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d195118 q = 0) : d195846 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d195118, d195846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d195118, d195846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d195161 q = 0) : d195877 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195161, d195877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195161, d195877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18582 q selected
  have h17 (q : Pattern) (selected : d195162 q = 0) : d195878 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195162, d195878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d195162, d195878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d195163 q = 0) : d195879 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195163, d195879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d195163, d195879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d195164 q = 0) : d195880 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195164, d195880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d195164, d195880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d195165 q = 0) : d195881 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d195165, d195881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d195165, d195881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d195166 q = 0) : d195882 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d195166, d195882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d195166, d195882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro18584 (p : Pattern) (selected : d195172 p = 0) : d195888 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195167 q = 0) : d195883 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d195167, d195883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195167, d195883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18583 q selected
  have h2 (q : Pattern) (selected : d195168 q = 0) : d195884 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d195168, d195884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195168, d195884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195169 q = 0) : d195885 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d195169, d195885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195169, d195885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d195170 q = 0) : d195886 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d195170, d195886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195170, d195886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d195171 q = 0) : d195887 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d195171, d195887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195171, d195887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195172 q = 0) : d195888 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d195172, d195888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195172, d195888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18585 (p : Pattern) (selected : d195181 p = 0) : d195897 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195177 q = 0) : d195893 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195177, d195893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6271 q selected
    | true =>
      simp only [d195177, d195893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15131 q selected
  have h2 (q : Pattern) (selected : d195178 q = 0) : d195894 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195178, d195894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195178, d195894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195179 q = 0) : d195895 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195179, d195895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195179, d195895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d195180 q = 0) : d195896 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d195180, d195896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195180, d195896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195181 q = 0) : d195897 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d195181, d195897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195181, d195897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro18586 (p : Pattern) (selected : d195187 p = 0) : d195903 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195182 q = 0) : d195898 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195182, d195898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18585 q selected
    | true =>
      simp only [d195182, d195898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195183 q = 0) : d195899 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195183, d195899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195183, d195899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195184 q = 0) : d195900 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195184, d195900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195184, d195900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195185 q = 0) : d195901 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195185, d195901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195185, d195901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195186 q = 0) : d195902 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195186, d195902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195186, d195902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195187 q = 0) : d195903 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195187, d195903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195187, d195903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18587 (p : Pattern) (selected : d195193 p = 0) : d195909 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195188 q = 0) : d195904 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195188, d195904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18586 q selected
    | true =>
      simp only [d195188, d195904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195189 q = 0) : d195905 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195189, d195905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195189, d195905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195190 q = 0) : d195906 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195190, d195906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195190, d195906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195191 q = 0) : d195907 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195191, d195907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195191, d195907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d195192 q = 0) : d195908 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195192, d195908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195192, d195908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195193 q = 0) : d195909 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195193, d195909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195193, d195909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18588 (p : Pattern) (selected : d195196 p = 0) : d195912 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195182 q = 0) : d195898 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195182, d195898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18585 q selected
    | true =>
      simp only [d195182, d195898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195183 q = 0) : d195899 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195183, d195899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195183, d195899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195184 q = 0) : d195900 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195184, d195900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195184, d195900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195185 q = 0) : d195901 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195185, d195901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195185, d195901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195186 q = 0) : d195902 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195186, d195902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195186, d195902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195196 q = 0) : d195912 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195196, d195912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195196, d195912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18589 (p : Pattern) (selected : d195202 p = 0) : d195918 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195188 q = 0) : d195904 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195188, d195904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18586 q selected
    | true =>
      simp only [d195188, d195904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195189 q = 0) : d195905 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195189, d195905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195189, d195905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195190 q = 0) : d195906 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195190, d195906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195190, d195906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195191 q = 0) : d195907 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195191, d195907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195191, d195907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d195192 q = 0) : d195908 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195192, d195908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195192, d195908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195197 q = 0) : d195913 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195197, d195913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18588 q selected
    | true =>
      simp only [d195197, d195913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d195198 q = 0) : d195914 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195198, d195914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195198, d195914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d195199 q = 0) : d195915 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195199, d195915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d195199, d195915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d195200 q = 0) : d195916 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195200, d195916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195200, d195916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d195201 q = 0) : d195917 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195201, d195917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195201, d195917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d195202 q = 0) : d195918 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195202, d195918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195202, d195918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro18590 (p : Pattern) (selected : d195207 p = 0) : d195923 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195182 q = 0) : d195898 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195182, d195898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18585 q selected
    | true =>
      simp only [d195182, d195898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195183 q = 0) : d195899 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195183, d195899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195183, d195899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195184 q = 0) : d195900 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195184, d195900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195184, d195900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195185 q = 0) : d195901 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195185, d195901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195185, d195901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195206 q = 0) : d195922 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195206, d195922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195206, d195922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195207 q = 0) : d195923 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195207, d195923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195207, d195923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18591 (p : Pattern) (selected : d195214 p = 0) : d195930 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195182 q = 0) : d195898 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195182, d195898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18585 q selected
    | true =>
      simp only [d195182, d195898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195183 q = 0) : d195899 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195183, d195899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195183, d195899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195184 q = 0) : d195900 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195184, d195900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195184, d195900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195212 q = 0) : d195928 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195212, d195928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195212, d195928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d195213 q = 0) : d195929 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195213, d195929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195213, d195929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195214 q = 0) : d195930 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195214, d195930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195214, d195930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18592 (p : Pattern) (selected : d195222 p = 0) : d195938 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195218 q = 0) : d195934 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195218, d195934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6286 q selected
    | true =>
      simp only [d195218, d195934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15139 q selected
  have h2 (q : Pattern) (selected : d195219 q = 0) : d195935 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195219, d195935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195219, d195935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195220 q = 0) : d195936 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195220, d195936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195220, d195936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d195177 q = 0) : d195893 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195177, d195893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6271 q selected
    | true =>
      simp only [d195177, d195893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15131 q selected
  have h5 (q : Pattern) (selected : d195178 q = 0) : d195894 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195178, d195894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195178, d195894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195179 q = 0) : d195895 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195179, d195895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195179, d195895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d195221 q = 0) : d195937 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d195221, d195937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195221, d195937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d195222 q = 0) : d195938 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d195222, d195938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d195222, d195938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro18593 (p : Pattern) (selected : d195228 p = 0) : d195944 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195223 q = 0) : d195939 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195223, d195939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18592 q selected
    | true =>
      simp only [d195223, d195939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195224 q = 0) : d195940 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195224, d195940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195224, d195940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195182 q = 0) : d195898 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195182, d195898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18585 q selected
    | true =>
      simp only [d195182, d195898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195183 q = 0) : d195899 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195183, d195899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195183, d195899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d195225 q = 0) : d195941 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195225, d195941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195225, d195941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195226 q = 0) : d195942 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195226, d195942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195226, d195942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d195227 q = 0) : d195943 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195227, d195943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d195227, d195943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d195228 q = 0) : d195944 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195228, d195944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195228, d195944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro18594 (p : Pattern) (selected : d195234 p = 0) : d195897 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195230 q = 0) : d195893 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195230, d195893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6291 q selected
    | true =>
      simp only [d195230, d195893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15144 q selected
  have h2 (q : Pattern) (selected : d195231 q = 0) : d195894 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195231, d195894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195231, d195894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195232 q = 0) : d195895 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195232, d195895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195232, d195895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d195233 q = 0) : d195896 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d195233, d195896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195233, d195896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195234 q = 0) : d195897 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d195234, d195897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195234, d195897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro18595 (p : Pattern) (selected : d195240 p = 0) : d195903 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195235 q = 0) : d195898 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195235, d195898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18594 q selected
    | true =>
      simp only [d195235, d195898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195236 q = 0) : d195899 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195236, d195899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195236, d195899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195237 q = 0) : d195900 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195237, d195900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195237, d195900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195238 q = 0) : d195901 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195238, d195901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195238, d195901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195239 q = 0) : d195902 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195239, d195902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195239, d195902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195240 q = 0) : d195903 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195240, d195903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195240, d195903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18596 (p : Pattern) (selected : d195247 p = 0) : d195951 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195208 q = 0) : d195924 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195208, d195924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18590 q selected
    | true =>
      simp only [d195208, d195924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195209 q = 0) : d195925 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195209, d195925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195209, d195925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195210 q = 0) : d195926 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195210, d195926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195210, d195926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195211 q = 0) : d195927 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195211, d195927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195211, d195927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d195215 q = 0) : d195931 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195215, d195931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18591 q selected
    | true =>
      simp only [d195215, d195931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195216 q = 0) : d195932 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195216, d195932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195216, d195932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d195217 q = 0) : d195933 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195217, d195933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d195217, d195933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d195229 q = 0) : d195945 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195229, d195945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18593 q selected
    | true =>
      simp only [d195229, d195945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18586 q selected
  have h9 (q : Pattern) (selected : d195241 q = 0) : d195904 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195241, d195904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18595 q selected
    | true =>
      simp only [d195241, d195904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d195242 q = 0) : d195946 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195242, d195946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d195242, d195946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d195188 q = 0) : d195904 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195188, d195904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18586 q selected
    | true =>
      simp only [d195188, d195904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d195243 q = 0) : d195947 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195243, d195947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d195243, d195947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d195244 q = 0) : d195948 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195244, d195948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d195244, d195948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d195245 q = 0) : d195949 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195245, d195949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d195245, d195949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d195246 q = 0) : d195950 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195246, d195950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195246, d195950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d195247 q = 0) : d195951 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195247, d195951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195247, d195951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro18597 (p : Pattern) (selected : d195248 p = 0) : d195952 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195182 q = 0) : d195898 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195182, d195898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18585 q selected
    | true =>
      simp only [d195182, d195898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195183 q = 0) : d195899 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195183, d195899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195183, d195899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195184 q = 0) : d195900 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195184, d195900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195184, d195900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195185 q = 0) : d195901 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195185, d195901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195185, d195901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195206 q = 0) : d195922 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195206, d195922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195206, d195922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195248 q = 0) : d195952 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195248, d195952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195248, d195952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18598 (p : Pattern) (selected : d195253 p = 0) : d195957 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195182 q = 0) : d195898 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195182, d195898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18585 q selected
    | true =>
      simp only [d195182, d195898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195183 q = 0) : d195899 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195183, d195899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195183, d195899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195184 q = 0) : d195900 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195184, d195900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195184, d195900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195212 q = 0) : d195928 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195212, d195928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195212, d195928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d195213 q = 0) : d195929 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195213, d195929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195213, d195929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195253 q = 0) : d195957 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195253, d195957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195253, d195957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18599 (p : Pattern) (selected : d195257 p = 0) : d195961 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195223 q = 0) : d195939 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195223, d195939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18592 q selected
    | true =>
      simp only [d195223, d195939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195224 q = 0) : d195940 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195224, d195940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195224, d195940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195182 q = 0) : d195898 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195182, d195898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18585 q selected
    | true =>
      simp only [d195182, d195898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195183 q = 0) : d195899 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195183, d195899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195183, d195899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d195225 q = 0) : d195941 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195225, d195941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195225, d195941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195226 q = 0) : d195942 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195226, d195942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195226, d195942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d195227 q = 0) : d195943 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195227, d195943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d195227, d195943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d195257 q = 0) : d195961 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195257, d195961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d195257, d195961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro18600 (p : Pattern) (selected : d195259 p = 0) : d195912 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195235 q = 0) : d195898 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195235, d195898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18594 q selected
    | true =>
      simp only [d195235, d195898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195236 q = 0) : d195899 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195236, d195899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195236, d195899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195237 q = 0) : d195900 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195237, d195900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195237, d195900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195238 q = 0) : d195901 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195238, d195901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195238, d195901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195239 q = 0) : d195902 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195239, d195902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195239, d195902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195259 q = 0) : d195912 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195259, d195912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195259, d195912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18601 (p : Pattern) (selected : d195266 p = 0) : d195968 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195208 q = 0) : d195924 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195208, d195924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18590 q selected
    | true =>
      simp only [d195208, d195924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195209 q = 0) : d195925 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195209, d195925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195209, d195925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195210 q = 0) : d195926 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195210, d195926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195210, d195926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195211 q = 0) : d195927 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195211, d195927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195211, d195927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d195215 q = 0) : d195931 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195215, d195931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18591 q selected
    | true =>
      simp only [d195215, d195931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195216 q = 0) : d195932 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195216, d195932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195216, d195932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d195217 q = 0) : d195933 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195217, d195933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d195217, d195933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d195229 q = 0) : d195945 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195229, d195945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18593 q selected
    | true =>
      simp only [d195229, d195945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18586 q selected
  have h9 (q : Pattern) (selected : d195241 q = 0) : d195904 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195241, d195904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18595 q selected
    | true =>
      simp only [d195241, d195904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d195242 q = 0) : d195946 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195242, d195946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d195242, d195946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d195188 q = 0) : d195904 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195188, d195904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18586 q selected
    | true =>
      simp only [d195188, d195904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d195243 q = 0) : d195947 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195243, d195947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d195243, d195947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d195244 q = 0) : d195948 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195244, d195948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d195244, d195948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d195245 q = 0) : d195949 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195245, d195949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d195245, d195949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d195246 q = 0) : d195950 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195246, d195950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195246, d195950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d195249 q = 0) : d195953 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195249, d195953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18597 q selected
    | true =>
      simp only [d195249, d195953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d195250 q = 0) : d195954 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195250, d195954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195250, d195954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d195251 q = 0) : d195955 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195251, d195955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d195251, d195955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d195252 q = 0) : d195956 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195252, d195956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195252, d195956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d195254 q = 0) : d195958 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195254, d195958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18598 q selected
    | true =>
      simp only [d195254, d195958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d195255 q = 0) : d195959 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195255, d195959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195255, d195959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d195256 q = 0) : d195960 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195256, d195960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d195256, d195960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d195258 q = 0) : d195962 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195258, d195962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18599 q selected
    | true =>
      simp only [d195258, d195962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18588 q selected
  have h24 (q : Pattern) (selected : d195260 q = 0) : d195913 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195260, d195913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18600 q selected
    | true =>
      simp only [d195260, d195913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d195261 q = 0) : d195963 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195261, d195963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d195261, d195963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d195197 q = 0) : d195913 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195197, d195913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18588 q selected
    | true =>
      simp only [d195197, d195913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d195262 q = 0) : d195964 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195262, d195964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d195262, d195964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d195263 q = 0) : d195965 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195263, d195965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d195263, d195965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d195264 q = 0) : d195966 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195264, d195966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d195264, d195966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d195265 q = 0) : d195967 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195265, d195967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d195265, d195967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d195266 q = 0) : d195968 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195266, d195968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d195266, d195968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro18602 (p : Pattern) (selected : d195268 p = 0) : d195970 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195188 q = 0) : d195904 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195188, d195904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18586 q selected
    | true =>
      simp only [d195188, d195904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195189 q = 0) : d195905 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195189, d195905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195189, d195905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195190 q = 0) : d195906 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195190, d195906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195190, d195906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195191 q = 0) : d195907 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195191, d195907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195191, d195907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d195192 q = 0) : d195908 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195192, d195908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195192, d195908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195268 q = 0) : d195970 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195268, d195970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195268, d195970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18603 (p : Pattern) (selected : d195275 p = 0) : d195977 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195258 q = 0) : d195962 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195258, d195962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18599 q selected
    | true =>
      simp only [d195258, d195962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18588 q selected
  have h2 (q : Pattern) (selected : d195260 q = 0) : d195913 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195260, d195913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18600 q selected
    | true =>
      simp only [d195260, d195913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d195261 q = 0) : d195963 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195261, d195963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195261, d195963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d195197 q = 0) : d195913 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195197, d195913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18588 q selected
    | true =>
      simp only [d195197, d195913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195262 q = 0) : d195964 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195262, d195964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195262, d195964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195263 q = 0) : d195965 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195263, d195965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195263, d195965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d195273 q = 0) : d195975 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195273, d195975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195273, d195975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d195274 q = 0) : d195976 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195274, d195976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195274, d195976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d195275 q = 0) : d195977 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195275, d195977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195275, d195977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro18604 (p : Pattern) (selected : d195288 p = 0) : d195990 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195281 q = 0) : d195983 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195281, d195983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6314 q selected
    | true =>
      simp only [d195281, d195983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15159 q selected
  have h2 (q : Pattern) (selected : d195282 q = 0) : d195984 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195282, d195984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195282, d195984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195283 q = 0) : d195985 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195283, d195985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195283, d195985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d195284 q = 0) : d195986 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195284, d195986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6315 q selected
    | true =>
      simp only [d195284, d195986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15158 q selected
  have h5 (q : Pattern) (selected : d195285 q = 0) : d195987 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195285, d195987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195285, d195987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195286 q = 0) : d195988 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195286, d195988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195286, d195988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d195287 q = 0) : d195989 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d195287, d195989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195287, d195989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d195288 q = 0) : d195990 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d195288, d195990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d195288, d195990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro18605 (p : Pattern) (selected : d195292 p = 0) : d195994 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195284 q = 0) : d195986 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195284, d195986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6315 q selected
    | true =>
      simp only [d195284, d195986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15158 q selected
  have h2 (q : Pattern) (selected : d195285 q = 0) : d195987 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195285, d195987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195285, d195987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195286 q = 0) : d195988 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195286, d195988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195286, d195988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d195291 q = 0) : d195993 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d195291, d195993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195291, d195993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195292 q = 0) : d195994 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d195292, d195994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195292, d195994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro18606 (p : Pattern) (selected : d195298 p = 0) : d196000 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195289 q = 0) : d195991 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195289, d195991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18604 q selected
    | true =>
      simp only [d195289, d195991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195290 q = 0) : d195992 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195290, d195992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195290, d195992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195293 q = 0) : d195995 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195293, d195995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18605 q selected
    | true =>
      simp only [d195293, d195995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195294 q = 0) : d195996 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195294, d195996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195294, d195996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d195295 q = 0) : d195997 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195295, d195997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195295, d195997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195296 q = 0) : d195998 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195296, d195998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195296, d195998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d195297 q = 0) : d195999 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195297, d195999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d195297, d195999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d195298 q = 0) : d196000 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195298, d196000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d195298, d196000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro18607 (p : Pattern) (selected : d195302 p = 0) : d196004 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195293 q = 0) : d195995 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195293, d195995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18605 q selected
    | true =>
      simp only [d195293, d195995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195294 q = 0) : d195996 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195294, d195996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195294, d195996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195299 q = 0) : d196001 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195299, d196001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195299, d196001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195300 q = 0) : d196002 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195300, d196002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195300, d196002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195301 q = 0) : d196003 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195301, d196003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195301, d196003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195302 q = 0) : d196004 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195302, d196004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195302, d196004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18608 (p : Pattern) (selected : d195308 p = 0) : d195994 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195304 q = 0) : d195986 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195304, d195986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6323 q selected
    | true =>
      simp only [d195304, d195986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15164 q selected
  have h2 (q : Pattern) (selected : d195305 q = 0) : d195987 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195305, d195987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195305, d195987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195306 q = 0) : d195988 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195306, d195988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195306, d195988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d195307 q = 0) : d195993 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d195307, d195993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195307, d195993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195308 q = 0) : d195994 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d195308, d195994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195308, d195994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro18609 (p : Pattern) (selected : d195314 p = 0) : d196004 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195309 q = 0) : d195995 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195309, d195995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18608 q selected
    | true =>
      simp only [d195309, d195995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195310 q = 0) : d195996 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195310, d195996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195310, d195996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195311 q = 0) : d196001 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195311, d196001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195311, d196001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195312 q = 0) : d196002 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195312, d196002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195312, d196002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195313 q = 0) : d196003 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195313, d196003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195313, d196003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195314 q = 0) : d196004 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195314, d196004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195314, d196004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18610 (p : Pattern) (selected : d195322 p = 0) : d196012 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195303 q = 0) : d196005 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195303, d196005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18606 q selected
    | true =>
      simp only [d195303, d196005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18607 q selected
  have h2 (q : Pattern) (selected : d195315 q = 0) : d196006 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195315, d196006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18609 q selected
    | true =>
      simp only [d195315, d196006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d195316 q = 0) : d196007 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195316, d196007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195316, d196007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d195317 q = 0) : d196006 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195317, d196006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18607 q selected
    | true =>
      simp only [d195317, d196006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195318 q = 0) : d196008 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195318, d196008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195318, d196008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195319 q = 0) : d196009 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195319, d196009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195319, d196009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d195320 q = 0) : d196010 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195320, d196010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195320, d196010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d195321 q = 0) : d196011 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195321, d196011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195321, d196011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d195322 q = 0) : d196012 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195322, d196012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195322, d196012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro18611 (p : Pattern) (selected : d195328 p = 0) : d196018 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195194 q = 0) : d195910 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195194, d195910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195194, d195910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18587 q selected
  have h2 (q : Pattern) (selected : d195195 q = 0) : d195911 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195195, d195911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195195, d195911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d195203 q = 0) : d195919 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195203, d195919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18587 q selected
    | true =>
      simp only [d195203, d195919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18589 q selected
  have h4 (q : Pattern) (selected : d195204 q = 0) : d195920 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195204, d195920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195204, d195920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195205 q = 0) : d195921 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195205, d195921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195205, d195921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195267 q = 0) : d195969 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195267, d195969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18596 q selected
    | true =>
      simp only [d195267, d195969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18601 q selected
  have h7 (q : Pattern) (selected : d195269 q = 0) : d195971 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195269, d195971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18602 q selected
    | true =>
      simp only [d195269, d195971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d195270 q = 0) : d195972 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195270, d195972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d195270, d195972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d195271 q = 0) : d195973 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195271, d195973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d195271, d195973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d195272 q = 0) : d195974 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195272, d195974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195272, d195974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d195276 q = 0) : d195978 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195276, d195978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195276, d195978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18603 q selected
  have h12 (q : Pattern) (selected : d195277 q = 0) : d195979 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195277, d195979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d195277, d195979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d195278 q = 0) : d195980 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195278, d195980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d195278, d195980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d195279 q = 0) : d195981 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195279, d195981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d195279, d195981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d195280 q = 0) : d195982 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d195280, d195982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d195280, d195982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d195323 q = 0) : d196013 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195323, d196013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195323, d196013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18610 q selected
  have h17 (q : Pattern) (selected : d195324 q = 0) : d196014 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195324, d196014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d195324, d196014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d195325 q = 0) : d196015 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195325, d196015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d195325, d196015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d195326 q = 0) : d196016 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195326, d196016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d195326, d196016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d195327 q = 0) : d196017 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d195327, d196017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d195327, d196017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d195328 q = 0) : d196018 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d195328, d196018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d195328, d196018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro18612 (p : Pattern) (selected : d195334 p = 0) : d196024 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195329 q = 0) : d196019 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d195329, d196019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195329, d196019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18611 q selected
  have h2 (q : Pattern) (selected : d195330 q = 0) : d196020 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d195330, d196020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195330, d196020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195331 q = 0) : d196021 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d195331, d196021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195331, d196021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d195332 q = 0) : d196022 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d195332, d196022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195332, d196022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d195333 q = 0) : d196023 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d195333, d196023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195333, d196023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195334 q = 0) : d196024 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d195334, d196024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195334, d196024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18613 (p : Pattern) (selected : d195340 p = 0) : d196030 p = 1 := by
  have h0 (q : Pattern) (selected : d194713 q = 0) : d195501 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194713, d195501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6039 q selected
    | true =>
      simp only [d194713, d195501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18502 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d194852 q = 0) : d195620 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194852, d195620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d194852, d195620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18528 q selected
  have h3 (q : Pattern) (selected : d194853 q = 0) : d195621 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d194853, d195621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194853, d195621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d195012 q = 0) : d195754 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d195012, d195754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195012, d195754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18556 q selected
  have h5 (q : Pattern) (selected : d195013 q = 0) : d195755 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d195013, d195755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195013, d195755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195014 q = 0) : d195756 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d195014, d195756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195014, d195756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d195173 q = 0) : d195889 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d195173, d195889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195173, d195889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18584 q selected
  have h8 (q : Pattern) (selected : d195174 q = 0) : d195890 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d195174, d195890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195174, d195890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d195175 q = 0) : d195891 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d195175, d195891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195175, d195891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d195176 q = 0) : d195892 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d195176, d195892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d195176, d195892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d195335 q = 0) : d196025 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d195335, d196025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195335, d196025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18612 q selected
  have h12 (q : Pattern) (selected : d195336 q = 0) : d196026 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d195336, d196026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195336, d196026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d195337 q = 0) : d196027 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d195337, d196027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195337, d196027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d195338 q = 0) : d196028 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d195338, d196028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195338, d196028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d195339 q = 0) : d196029 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d195339, d196029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d195339, d196029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d195340 q = 0) : d196030 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d195340, d196030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d195340, d196030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro18614 (p : Pattern) (selected : d195346 p = 0) : d196036 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195341 q = 0) : d196031 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d195341, d196031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18613 q selected
    | true =>
      simp only [d195341, d196031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195342 q = 0) : d196032 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d195342, d196032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195342, d196032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d195343 q = 0) : d196033 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d195343, d196033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195343, d196033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195344 q = 0) : d196034 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d195344, d196034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195344, d196034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195345 q = 0) : d196035 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d195345, d196035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195345, d196035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195346 q = 0) : d196036 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d195346, d196036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195346, d196036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18615 (p : Pattern) (selected : d195352 p = 0) : d196042 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195347 q = 0) : d196037 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d195347, d196037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18614 q selected
    | true =>
      simp only [d195347, d196037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195348 q = 0) : d196038 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d195348, d196038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195348, d196038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d195349 q = 0) : d196039 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d195349, d196039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195349, d196039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195350 q = 0) : d196040 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d195350, d196040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195350, d196040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195351 q = 0) : d196041 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d195351, d196041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195351, d196041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195352 q = 0) : d196042 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d195352, d196042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195352, d196042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18616 (p : Pattern) (selected : d195358 p = 0) : d196048 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195353 q = 0) : d196043 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d195353, d196043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18615 q selected
    | true =>
      simp only [d195353, d196043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195354 q = 0) : d196044 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d195354, d196044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195354, d196044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d195355 q = 0) : d196045 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d195355, d196045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195355, d196045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195356 q = 0) : d196046 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d195356, d196046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195356, d196046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195357 q = 0) : d196047 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d195357, d196047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195357, d196047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195358 q = 0) : d196048 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d195358, d196048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195358, d196048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18617 (p : Pattern) (selected : d195364 p = 0) : d196054 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195359 q = 0) : d196049 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d195359, d196049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18616 q selected
    | true =>
      simp only [d195359, d196049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195360 q = 0) : d196050 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d195360, d196050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195360, d196050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d195361 q = 0) : d196051 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d195361, d196051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195361, d196051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195362 q = 0) : d196052 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d195362, d196052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195362, d196052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195363 q = 0) : d196053 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d195363, d196053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195363, d196053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195364 q = 0) : d196054 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d195364, d196054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195364, d196054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18618 (p : Pattern) (selected : d195370 p = 0) : d196060 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195365 q = 0) : d196055 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d195365, d196055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18617 q selected
    | true =>
      simp only [d195365, d196055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195366 q = 0) : d196056 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d195366, d196056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195366, d196056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d195367 q = 0) : d196057 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d195367, d196057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195367, d196057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195368 q = 0) : d196058 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d195368, d196058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195368, d196058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195369 q = 0) : d196059 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d195369, d196059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195369, d196059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195370 q = 0) : d196060 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d195370, d196060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195370, d196060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18619 (p : Pattern) (selected : d195376 p = 0) : d196066 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195371 q = 0) : d196061 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d195371, d196061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18618 q selected
    | true =>
      simp only [d195371, d196061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195372 q = 0) : d196062 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d195372, d196062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195372, d196062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d195373 q = 0) : d196063 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d195373, d196063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195373, d196063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195374 q = 0) : d196064 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d195374, d196064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195374, d196064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195375 q = 0) : d196065 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d195375, d196065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195375, d196065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195376 q = 0) : d196066 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d195376, d196066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195376, d196066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18620 (p : Pattern) (selected : d195382 p = 0) : d196072 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d195377 q = 0) : d196067 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d195377, d196067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18619 q selected
    | true =>
      simp only [d195377, d196067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195378 q = 0) : d196068 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d195378, d196068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195378, d196068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d195379 q = 0) : d196069 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d195379, d196069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195379, d196069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195380 q = 0) : d196070 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d195380, d196070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195380, d196070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195381 q = 0) : d196071 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d195381, d196071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195381, d196071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195382 q = 0) : d196072 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d195382, d196072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195382, d196072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18621 (p : Pattern) (selected : d194622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d94995 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d94995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6358 q selected
    | true =>
      simp only [d94995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6345 q selected
  have h2 (q : Pattern) (selected : d94996 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d94996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d94996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d94997 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d94997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d94997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d194621 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d194621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194622 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d194622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro18622 (p : Pattern) (selected : d194628 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d194623 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18621 q selected
    | true =>
      simp only [d194623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d194624 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194625 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194626 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194627 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d194628 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18623 (p : Pattern) (selected : d194635 p = 1) : d198218 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d194602 q = 1) : d194602 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d194608 q = 1) : d194608 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d194620 q = 1) : d194620 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d194629 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18622 q selected
    | true =>
      simp only [d194629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194630 q = 1) : d198214 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194630, d198214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194630, d198214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194631 q = 1) : d194631 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d194632 q = 1) : d198215 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194632, d198215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d194632, d198215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d194633 q = 1) : d198216 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194633, d198216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194633, d198216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d194634 q = 1) : d198217 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194634, d198217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d194634, d198217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d194635 q = 1) : d198218 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194635, d198218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194635, d198218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro18624 (p : Pattern) (selected : d194647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d194623 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18621 q selected
    | true =>
      simp only [d194623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d194624 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194625 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194626 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194627 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d194647 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d194647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18625 (p : Pattern) (selected : d194654 p = 1) : d198223 p = 1 := by
  have h0 (q : Pattern) (selected : d194602 q = 1) : d194602 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d194608 q = 1) : d194608 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d194620 q = 1) : d194620 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d194629 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18622 q selected
    | true =>
      simp only [d194629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d194630 q = 1) : d198214 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194630, d198214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194630, d198214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194631 q = 1) : d194631 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d194632 q = 1) : d198215 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194632, d198215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d194632, d198215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d194633 q = 1) : d198216 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194633, d198216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d194633, d198216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d194634 q = 1) : d198217 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194634, d198217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194634, d198217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d194640 q = 1) : d194640 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d194644 q = 1) : d194644 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d194646 q = 1) : d194646 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d194648 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18624 q selected
    | true =>
      simp only [d194648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d194649 q = 1) : d198219 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194649, d198219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d194649, d198219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d194650 q = 1) : d194650 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d194651 q = 1) : d198220 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194651, d198220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d194651, d198220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d194652 q = 1) : d198221 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194652, d198221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d194652, d198221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d194653 q = 1) : d198222 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194653, d198222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d194653, d198222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d194654 q = 1) : d198223 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194654, d198223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d194654, d198223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro18626 (p : Pattern) (selected : d194663 p = 1) : d198230 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d194646 q = 1) : d194646 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d194648 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18624 q selected
    | true =>
      simp only [d194648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d194649 q = 1) : d198219 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194649, d198219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d194649, d198219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d194650 q = 1) : d194650 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d194651 q = 1) : d198220 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194651, d198220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194651, d198220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194661 q = 1) : d198228 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194661, d198228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194661, d198228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d194662 q = 1) : d198229 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194662, d198229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194662, d198229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d194663 q = 1) : d198230 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194663, d198230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194663, d198230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro18627 (p : Pattern) (selected : d194686 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95081 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6365 q selected
    | true =>
      simp only [d95081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6352 q selected
  have h2 (q : Pattern) (selected : d95082 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95083 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d194685 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d194685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194686 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d194686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro18628 (p : Pattern) (selected : d194692 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d194687 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18627 q selected
    | true =>
      simp only [d194687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d194688 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194689 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194690 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194691 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d194692 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d194692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18629 (p : Pattern) (selected : d194700 p = 1) : d198240 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d194684 q = 1) : d194684 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d194693 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18628 q selected
    | true =>
      simp only [d194693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d194694 q = 1) : d198236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194694, d198236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d194694, d198236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d194696 q = 1) : d194696 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d194697 q = 1) : d198237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194697, d198237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194697, d198237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194698 q = 1) : d198238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194698, d198238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194698, d198238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d194699 q = 1) : d198239 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194699, d198239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194699, d198239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d194700 q = 1) : d198240 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194700, d198240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194700, d198240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro18630 (p : Pattern) (selected : d194706 p = 1) : d198246 p = 1 := by
  have h0 (q : Pattern) (selected : d194596 q = 1) : d194596 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d194655 q = 1) : d198224 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194655, d198224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18623 q selected
    | true =>
      simp only [d194655, d198224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18625 q selected
  have h2 (q : Pattern) (selected : d194657 q = 1) : d194657 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d194658 q = 1) : d198225 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194658, d198225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d194658, d198225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d194659 q = 1) : d198226 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194659, d198226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194659, d198226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194660 q = 1) : d198227 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194660, d198227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194660, d198227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d194664 q = 1) : d198231 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194664, d198231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194664, d198231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18626 q selected
  have h8 (q : Pattern) (selected : d194665 q = 1) : d198232 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194665, d198232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d194665, d198232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d194666 q = 1) : d198233 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194666, d198233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d194666, d198233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d194667 q = 1) : d198234 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194667, d198234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d194667, d198234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d194668 q = 1) : d198235 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194668, d198235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d194668, d198235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d194701 q = 1) : d198241 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194701, d198241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194701, d198241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18629 q selected
  have h13 (q : Pattern) (selected : d194702 q = 1) : d198242 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194702, d198242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d194702, d198242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d194703 q = 1) : d198243 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194703, d198243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d194703, d198243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d194704 q = 1) : d198244 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194704, d198244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d194704, d198244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d194705 q = 1) : d198245 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194705, d198245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d194705, d198245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d194706 q = 1) : d198246 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194706, d198246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d194706, d198246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro18631 (p : Pattern) (selected : d194712 p = 1) : d198252 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d194707 q = 1) : d198247 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194707, d198247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194707, d198247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18630 q selected
  have h2 (q : Pattern) (selected : d194708 q = 1) : d198248 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194708, d198248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194708, d198248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194709 q = 1) : d198249 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194709, d198249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194709, d198249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d194710 q = 1) : d198250 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194710, d198250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194710, d198250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d194711 q = 1) : d198251 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194711, d198251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194711, d198251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194712 q = 1) : d198252 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194712, d198252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194712, d198252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18632 (p : Pattern) (selected : d194761 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95201 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6371 q selected
    | true =>
      simp only [d95201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6372 q selected
  have h2 (q : Pattern) (selected : d95202 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95203 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d194760 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d194760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194761 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d194761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro18633 (p : Pattern) (selected : d194767 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d194762 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18632 q selected
    | true =>
      simp only [d194762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d194763 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194764 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194765 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194766 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d194767 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18634 (p : Pattern) (selected : d194774 p = 1) : d198258 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d194741 q = 1) : d194741 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d194747 q = 1) : d194747 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d194759 q = 1) : d194759 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d194768 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18633 q selected
    | true =>
      simp only [d194768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194769 q = 1) : d198254 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194769, d198254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194769, d198254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194770 q = 1) : d194770 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d194771 q = 1) : d198255 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194771, d198255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d194771, d198255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d194772 q = 1) : d198256 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194772, d198256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194772, d198256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d194773 q = 1) : d198257 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194773, d198257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d194773, d198257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d194774 q = 1) : d198258 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194774, d198258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194774, d198258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro18635 (p : Pattern) (selected : d194786 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d194762 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18632 q selected
    | true =>
      simp only [d194762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d194763 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194764 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194765 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194766 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d194786 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d194786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18636 (p : Pattern) (selected : d194793 p = 1) : d198263 p = 1 := by
  have h0 (q : Pattern) (selected : d194741 q = 1) : d194741 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d194747 q = 1) : d194747 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d194759 q = 1) : d194759 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d194768 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18633 q selected
    | true =>
      simp only [d194768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d194769 q = 1) : d198254 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194769, d198254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194769, d198254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194770 q = 1) : d194770 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d194771 q = 1) : d198255 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194771, d198255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d194771, d198255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d194772 q = 1) : d198256 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194772, d198256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d194772, d198256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d194773 q = 1) : d198257 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194773, d198257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194773, d198257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d194779 q = 1) : d194779 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d194783 q = 1) : d194783 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d194785 q = 1) : d194785 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d194787 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18635 q selected
    | true =>
      simp only [d194787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d194788 q = 1) : d198259 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194788, d198259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d194788, d198259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d194789 q = 1) : d194789 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d194790 q = 1) : d198260 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194790, d198260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d194790, d198260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d194791 q = 1) : d198261 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194791, d198261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d194791, d198261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d194792 q = 1) : d198262 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194792, d198262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d194792, d198262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d194793 q = 1) : d198263 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194793, d198263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d194793, d198263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro18637 (p : Pattern) (selected : d194802 p = 1) : d198270 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d194785 q = 1) : d194785 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d194787 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18635 q selected
    | true =>
      simp only [d194787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d194788 q = 1) : d198259 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194788, d198259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d194788, d198259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d194789 q = 1) : d194789 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d194790 q = 1) : d198260 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194790, d198260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194790, d198260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194800 q = 1) : d198268 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194800, d198268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194800, d198268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d194801 q = 1) : d198269 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194801, d198269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194801, d198269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d194802 q = 1) : d198270 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194802, d198270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194802, d198270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro18638 (p : Pattern) (selected : d194825 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95322 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6382 q selected
    | true =>
      simp only [d95322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6383 q selected
  have h2 (q : Pattern) (selected : d95323 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95324 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d194824 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d194824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194825 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d194825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro18639 (p : Pattern) (selected : d194831 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d194826 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18638 q selected
    | true =>
      simp only [d194826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d194827 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194828 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194829 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194830 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d194831 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d194831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18640 (p : Pattern) (selected : d194839 p = 1) : d198280 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d194823 q = 1) : d194823 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d194832 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18639 q selected
    | true =>
      simp only [d194832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d194833 q = 1) : d198276 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194833, d198276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d194833, d198276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d194835 q = 1) : d194835 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d194836 q = 1) : d198277 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194836, d198277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194836, d198277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194837 q = 1) : d198278 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194837, d198278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194837, d198278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d194838 q = 1) : d198279 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194838, d198279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194838, d198279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d194839 q = 1) : d198280 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194839, d198280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194839, d198280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro18641 (p : Pattern) (selected : d194845 p = 1) : d198286 p = 1 := by
  have h0 (q : Pattern) (selected : d194735 q = 1) : d194735 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d194794 q = 1) : d198264 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194794, d198264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18634 q selected
    | true =>
      simp only [d194794, d198264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18636 q selected
  have h2 (q : Pattern) (selected : d194796 q = 1) : d194796 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d194797 q = 1) : d198265 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194797, d198265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d194797, d198265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d194798 q = 1) : d198266 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194798, d198266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194798, d198266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194799 q = 1) : d198267 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194799, d198267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194799, d198267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d194803 q = 1) : d198271 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194803, d198271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194803, d198271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18637 q selected
  have h8 (q : Pattern) (selected : d194804 q = 1) : d198272 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194804, d198272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d194804, d198272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d194805 q = 1) : d198273 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194805, d198273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d194805, d198273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d194806 q = 1) : d198274 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194806, d198274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d194806, d198274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d194807 q = 1) : d198275 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194807, d198275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d194807, d198275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d194840 q = 1) : d198281 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194840, d198281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194840, d198281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18640 q selected
  have h13 (q : Pattern) (selected : d194841 q = 1) : d198282 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194841, d198282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d194841, d198282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d194842 q = 1) : d198283 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194842, d198283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d194842, d198283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d194843 q = 1) : d198284 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194843, d198284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d194843, d198284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d194844 q = 1) : d198285 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194844, d198285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d194844, d198285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d194845 q = 1) : d198286 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194845, d198286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d194845, d198286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro18642 (p : Pattern) (selected : d194851 p = 1) : d198292 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d194846 q = 1) : d198287 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194846, d198287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194846, d198287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18641 q selected
  have h2 (q : Pattern) (selected : d194847 q = 1) : d198288 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194847, d198288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194847, d198288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194848 q = 1) : d198289 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194848, d198289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194848, d198289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d194849 q = 1) : d198290 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194849, d198290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194849, d198290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d194850 q = 1) : d198291 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194850, d198291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194850, d198291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194851 q = 1) : d198292 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194851, d198292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194851, d198292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18643 (p : Pattern) (selected : d194911 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d194907 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d194907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6391 q selected
    | true =>
      simp only [d194907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15192 q selected
  have h2 (q : Pattern) (selected : d194908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d194908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194909 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d194909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d194910 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d194910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194911 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d194911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro18644 (p : Pattern) (selected : d194917 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d194912 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18643 q selected
    | true =>
      simp only [d194912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d194913 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194914 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194915 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194916 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d194917 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18645 (p : Pattern) (selected : d194924 p = 1) : d198299 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d194888 q = 1) : d194888 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d194894 q = 1) : d194894 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d194906 q = 1) : d194906 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d194918 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18644 q selected
    | true =>
      simp only [d194918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194919 q = 1) : d198295 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194919, d198295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194919, d198295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194920 q = 1) : d194920 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d194921 q = 1) : d198296 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194921, d198296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d194921, d198296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d194922 q = 1) : d198297 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194922, d198297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194922, d198297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d194923 q = 1) : d198298 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194923, d198298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d194923, d198298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d194924 q = 1) : d198299 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194924, d198299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194924, d198299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro18646 (p : Pattern) (selected : d194936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d194912 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18643 q selected
    | true =>
      simp only [d194912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d194913 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194914 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194915 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194916 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d194936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d194936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18647 (p : Pattern) (selected : d194943 p = 1) : d198304 p = 1 := by
  have h0 (q : Pattern) (selected : d194888 q = 1) : d194888 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d194894 q = 1) : d194894 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d194906 q = 1) : d194906 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d194918 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18644 q selected
    | true =>
      simp only [d194918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d194919 q = 1) : d198295 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194919, d198295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194919, d198295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194920 q = 1) : d194920 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d194921 q = 1) : d198296 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194921, d198296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d194921, d198296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d194922 q = 1) : d198297 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194922, d198297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d194922, d198297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d194923 q = 1) : d198298 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194923, d198298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194923, d198298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d194929 q = 1) : d194929 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d194933 q = 1) : d194933 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d194935 q = 1) : d194935 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d194937 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18646 q selected
    | true =>
      simp only [d194937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d194938 q = 1) : d198300 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194938, d198300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d194938, d198300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d194939 q = 1) : d194939 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d194940 q = 1) : d198301 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194940, d198301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d194940, d198301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d194941 q = 1) : d198302 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194941, d198302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d194941, d198302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d194942 q = 1) : d198303 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194942, d198303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d194942, d198303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d194943 q = 1) : d198304 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194943, d198304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d194943, d198304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro18648 (p : Pattern) (selected : d194952 p = 1) : d198311 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d194935 q = 1) : d194935 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d194937 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18646 q selected
    | true =>
      simp only [d194937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d194938 q = 1) : d198300 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194938, d198300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d194938, d198300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d194939 q = 1) : d194939 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d194940 q = 1) : d198301 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194940, d198301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194940, d198301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194950 q = 1) : d198309 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194950, d198309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194950, d198309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d194951 q = 1) : d198310 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194951, d198310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194951, d198310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d194952 q = 1) : d198311 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194952, d198311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194952, d198311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro18649 (p : Pattern) (selected : d194985 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d194981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d194981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6403 q selected
    | true =>
      simp only [d194981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15199 q selected
  have h2 (q : Pattern) (selected : d194982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d194982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d194983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d194984 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d194984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194985 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d194985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro18650 (p : Pattern) (selected : d194991 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d194986 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18649 q selected
    | true =>
      simp only [d194986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d194987 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d194988 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d194988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d194989 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d194990 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d194991 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d194991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18651 (p : Pattern) (selected : d194999 p = 1) : d198321 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d194980 q = 1) : d194980 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d194992 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18650 q selected
    | true =>
      simp only [d194992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d194993 q = 1) : d198317 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194993, d198317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d194993, d198317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d194995 q = 1) : d194995 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d194996 q = 1) : d198318 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194996, d198318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194996, d198318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194997 q = 1) : d198319 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194997, d198319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194997, d198319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d194998 q = 1) : d198320 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194998, d198320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194998, d198320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d194999 q = 1) : d198321 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194999, d198321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194999, d198321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro18652 (p : Pattern) (selected : d195005 p = 1) : d198327 p = 1 := by
  have h0 (q : Pattern) (selected : d194882 q = 1) : d194882 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d194944 q = 1) : d198305 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194944, d198305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18645 q selected
    | true =>
      simp only [d194944, d198305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18647 q selected
  have h2 (q : Pattern) (selected : d194946 q = 1) : d194946 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d194947 q = 1) : d198306 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194947, d198306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d194947, d198306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d194948 q = 1) : d198307 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194948, d198307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d194948, d198307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d194949 q = 1) : d198308 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194949, d198308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194949, d198308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d194953 q = 1) : d198312 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194953, d198312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d194953, d198312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18648 q selected
  have h8 (q : Pattern) (selected : d194954 q = 1) : d198313 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194954, d198313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d194954, d198313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d194955 q = 1) : d198314 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194955, d198314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d194955, d198314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d194956 q = 1) : d198315 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194956, d198315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d194956, d198315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d194957 q = 1) : d198316 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194957, d198316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d194957, d198316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d195000 q = 1) : d198322 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195000, d198322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195000, d198322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18651 q selected
  have h13 (q : Pattern) (selected : d195001 q = 1) : d198323 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195001, d198323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d195001, d198323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d195002 q = 1) : d198324 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195002, d198324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d195002, d198324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d195003 q = 1) : d198325 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195003, d198325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d195003, d198325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d195004 q = 1) : d198326 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d195004, d198326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d195004, d198326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d195005 q = 1) : d198327 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d195005, d198327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d195005, d198327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro18653 (p : Pattern) (selected : d195011 p = 1) : d198333 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d195006 q = 1) : d198328 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d195006, d198328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195006, d198328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18652 q selected
  have h2 (q : Pattern) (selected : d195007 q = 1) : d198329 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d195007, d198329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195007, d198329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195008 q = 1) : d198330 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d195008, d198330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195008, d198330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d195009 q = 1) : d198331 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d195009, d198331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195009, d198331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d195010 q = 1) : d198332 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d195010, d198332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195010, d198332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195011 q = 1) : d198333 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d195011, d198333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195011, d198333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18654 (p : Pattern) (selected : d195072 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d195068 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6413 q selected
    | true =>
      simp only [d195068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15205 q selected
  have h2 (q : Pattern) (selected : d195069 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195070 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d195071 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d195071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195072 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d195072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro18655 (p : Pattern) (selected : d195078 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d195073 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18654 q selected
    | true =>
      simp only [d195073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195074 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195075 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195076 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195077 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195078 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18656 (p : Pattern) (selected : d195085 p = 1) : d198341 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d195049 q = 1) : d195049 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d195055 q = 1) : d195055 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d195067 q = 1) : d195067 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d195079 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18655 q selected
    | true =>
      simp only [d195079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195080 q = 1) : d198337 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195080, d198337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195080, d198337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195081 q = 1) : d195081 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d195082 q = 1) : d198338 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195082, d198338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195082, d198338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d195083 q = 1) : d198339 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195083, d198339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195083, d198339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d195084 q = 1) : d198340 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195084, d198340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195084, d198340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d195085 q = 1) : d198341 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195085, d198341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195085, d198341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro18657 (p : Pattern) (selected : d195097 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d195073 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18654 q selected
    | true =>
      simp only [d195073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195074 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195075 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195076 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195077 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195097 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18658 (p : Pattern) (selected : d195104 p = 1) : d198346 p = 1 := by
  have h0 (q : Pattern) (selected : d195049 q = 1) : d195049 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d195055 q = 1) : d195055 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d195067 q = 1) : d195067 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d195079 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18655 q selected
    | true =>
      simp only [d195079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d195080 q = 1) : d198337 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195080, d198337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195080, d198337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195081 q = 1) : d195081 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d195082 q = 1) : d198338 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195082, d198338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195082, d198338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d195083 q = 1) : d198339 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195083, d198339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195083, d198339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d195084 q = 1) : d198340 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195084, d198340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195084, d198340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d195090 q = 1) : d195090 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d195094 q = 1) : d195094 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d195096 q = 1) : d195096 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d195098 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18657 q selected
    | true =>
      simp only [d195098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d195099 q = 1) : d198342 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195099, d198342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d195099, d198342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d195100 q = 1) : d195100 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d195101 q = 1) : d198343 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195101, d198343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d195101, d198343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d195102 q = 1) : d198344 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195102, d198344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d195102, d198344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d195103 q = 1) : d198345 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195103, d198345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d195103, d198345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d195104 q = 1) : d198346 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195104, d198346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d195104, d198346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro18659 (p : Pattern) (selected : d195113 p = 1) : d198353 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d195096 q = 1) : d195096 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d195098 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18657 q selected
    | true =>
      simp only [d195098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d195099 q = 1) : d198342 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195099, d198342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195099, d198342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d195100 q = 1) : d195100 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d195101 q = 1) : d198343 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195101, d198343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195101, d198343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195111 q = 1) : d198351 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195111, d198351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195111, d198351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d195112 q = 1) : d198352 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195112, d198352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195112, d198352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d195113 q = 1) : d198353 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195113, d198353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195113, d198353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro18660 (p : Pattern) (selected : d195146 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d195142 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6425 q selected
    | true =>
      simp only [d195142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15212 q selected
  have h2 (q : Pattern) (selected : d195143 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195144 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d195145 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d195145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195146 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d195146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro18661 (p : Pattern) (selected : d195152 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d195147 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18660 q selected
    | true =>
      simp only [d195147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195148 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195149 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195150 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195151 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195152 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18662 (p : Pattern) (selected : d195160 p = 1) : d198363 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d195141 q = 1) : d195141 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d195153 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18661 q selected
    | true =>
      simp only [d195153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d195154 q = 1) : d198359 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195154, d198359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195154, d198359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d195156 q = 1) : d195156 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d195157 q = 1) : d198360 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195157, d198360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195157, d198360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195158 q = 1) : d198361 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195158, d198361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195158, d198361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d195159 q = 1) : d198362 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195159, d198362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195159, d198362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d195160 q = 1) : d198363 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195160, d198363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195160, d198363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro18663 (p : Pattern) (selected : d195166 p = 1) : d198369 p = 1 := by
  have h0 (q : Pattern) (selected : d195043 q = 1) : d195043 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d195105 q = 1) : d198347 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195105, d198347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18656 q selected
    | true =>
      simp only [d195105, d198347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18658 q selected
  have h2 (q : Pattern) (selected : d195107 q = 1) : d195107 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d195108 q = 1) : d198348 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195108, d198348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195108, d198348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d195109 q = 1) : d198349 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195109, d198349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195109, d198349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195110 q = 1) : d198350 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195110, d198350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195110, d198350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d195114 q = 1) : d198354 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195114, d198354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195114, d198354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18659 q selected
  have h8 (q : Pattern) (selected : d195115 q = 1) : d198355 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195115, d198355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d195115, d198355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d195116 q = 1) : d198356 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195116, d198356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d195116, d198356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d195117 q = 1) : d198357 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195117, d198357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d195117, d198357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d195118 q = 1) : d198358 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d195118, d198358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d195118, d198358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d195161 q = 1) : d198364 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195161, d198364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195161, d198364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18662 q selected
  have h13 (q : Pattern) (selected : d195162 q = 1) : d198365 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195162, d198365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d195162, d198365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d195163 q = 1) : d198366 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195163, d198366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d195163, d198366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d195164 q = 1) : d198367 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195164, d198367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d195164, d198367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d195165 q = 1) : d198368 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d195165, d198368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d195165, d198368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d195166 q = 1) : d198369 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d195166, d198369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d195166, d198369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro18664 (p : Pattern) (selected : d195172 p = 1) : d198375 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d195167 q = 1) : d198370 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d195167, d198370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195167, d198370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18663 q selected
  have h2 (q : Pattern) (selected : d195168 q = 1) : d198371 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d195168, d198371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195168, d198371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195169 q = 1) : d198372 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d195169, d198372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195169, d198372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d195170 q = 1) : d198373 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d195170, d198373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195170, d198373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d195171 q = 1) : d198374 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d195171, d198374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195171, d198374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195172 q = 1) : d198375 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d195172, d198375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195172, d198375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18665 (p : Pattern) (selected : d195234 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d195230 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6435 q selected
    | true =>
      simp only [d195230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15218 q selected
  have h2 (q : Pattern) (selected : d195231 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195232 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d195233 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d195233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195234 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d195234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro18666 (p : Pattern) (selected : d195240 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d195235 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18665 q selected
    | true =>
      simp only [d195235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195236 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195237 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195238 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195239 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195240 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18667 (p : Pattern) (selected : d195247 p = 1) : d198384 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d195211 q = 1) : d195211 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d195217 q = 1) : d195217 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d195229 q = 1) : d195229 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d195241 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18666 q selected
    | true =>
      simp only [d195241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195242 q = 1) : d198380 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195242, d198380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195242, d198380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195243 q = 1) : d195243 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d195244 q = 1) : d198381 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195244, d198381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195244, d198381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d195245 q = 1) : d198382 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195245, d198382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195245, d198382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d195246 q = 1) : d198383 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195246, d198383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195246, d198383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d195247 q = 1) : d198384 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195247, d198384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195247, d198384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro18668 (p : Pattern) (selected : d195259 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d195235 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18665 q selected
    | true =>
      simp only [d195235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195236 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195237 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195238 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195239 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195259 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18669 (p : Pattern) (selected : d195266 p = 1) : d198389 p = 1 := by
  have h0 (q : Pattern) (selected : d195211 q = 1) : d195211 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d195217 q = 1) : d195217 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d195229 q = 1) : d195229 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d195241 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18666 q selected
    | true =>
      simp only [d195241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d195242 q = 1) : d198380 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195242, d198380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195242, d198380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195243 q = 1) : d195243 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d195244 q = 1) : d198381 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195244, d198381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195244, d198381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d195245 q = 1) : d198382 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195245, d198382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195245, d198382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d195246 q = 1) : d198383 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195246, d198383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195246, d198383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d195252 q = 1) : d195252 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d195256 q = 1) : d195256 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d195258 q = 1) : d195258 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d195260 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18668 q selected
    | true =>
      simp only [d195260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d195261 q = 1) : d198385 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195261, d198385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d195261, d198385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d195262 q = 1) : d195262 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d195263 q = 1) : d198386 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195263, d198386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d195263, d198386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d195264 q = 1) : d198387 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195264, d198387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d195264, d198387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d195265 q = 1) : d198388 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195265, d198388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d195265, d198388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d195266 q = 1) : d198389 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195266, d198389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d195266, d198389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro18670 (p : Pattern) (selected : d195275 p = 1) : d198396 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d195258 q = 1) : d195258 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d195260 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18668 q selected
    | true =>
      simp only [d195260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d195261 q = 1) : d198385 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195261, d198385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195261, d198385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d195262 q = 1) : d195262 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d195263 q = 1) : d198386 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195263, d198386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195263, d198386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195273 q = 1) : d198394 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195273, d198394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195273, d198394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d195274 q = 1) : d198395 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195274, d198395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195274, d198395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d195275 q = 1) : d198396 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195275, d198396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195275, d198396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro18671 (p : Pattern) (selected : d195308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d195304 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d195304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6447 q selected
    | true =>
      simp only [d195304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15225 q selected
  have h2 (q : Pattern) (selected : d195305 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d195305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195306 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d195306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d195307 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d195307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195308 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d195308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro18672 (p : Pattern) (selected : d195314 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d195309 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d195309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18671 q selected
    | true =>
      simp only [d195309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195310 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d195310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195311 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d195311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195312 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d195312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195313 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d195313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195314 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d195314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18673 (p : Pattern) (selected : d195322 p = 1) : d198406 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d195303 q = 1) : d195303 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d195315 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18672 q selected
    | true =>
      simp only [d195315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d195316 q = 1) : d198402 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d195316, d198402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195316, d198402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d195318 q = 1) : d195318 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d195319 q = 1) : d198403 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d195319, d198403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195319, d198403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195320 q = 1) : d198404 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d195320, d198404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195320, d198404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d195321 q = 1) : d198405 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d195321, d198405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195321, d198405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d195322 q = 1) : d198406 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d195322, d198406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195322, d198406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro18674 (p : Pattern) (selected : d195328 p = 1) : d198412 p = 1 := by
  have h0 (q : Pattern) (selected : d195205 q = 1) : d195205 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d195267 q = 1) : d198390 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195267, d198390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18667 q selected
    | true =>
      simp only [d195267, d198390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18669 q selected
  have h2 (q : Pattern) (selected : d195269 q = 1) : d195269 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d195270 q = 1) : d198391 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195270, d198391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195270, d198391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d195271 q = 1) : d198392 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195271, d198392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195271, d198392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195272 q = 1) : d198393 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195272, d198393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195272, d198393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d195276 q = 1) : d198397 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195276, d198397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195276, d198397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18670 q selected
  have h8 (q : Pattern) (selected : d195277 q = 1) : d198398 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195277, d198398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d195277, d198398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d195278 q = 1) : d198399 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195278, d198399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d195278, d198399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d195279 q = 1) : d198400 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195279, d198400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d195279, d198400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d195280 q = 1) : d198401 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d195280, d198401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d195280, d198401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d195323 q = 1) : d198407 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d195323, d198407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195323, d198407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18673 q selected
  have h13 (q : Pattern) (selected : d195324 q = 1) : d198408 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d195324, d198408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d195324, d198408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d195325 q = 1) : d198409 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d195325, d198409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d195325, d198409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d195326 q = 1) : d198410 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d195326, d198410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d195326, d198410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d195327 q = 1) : d198411 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d195327, d198411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d195327, d198411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d195328 q = 1) : d198412 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d195328, d198412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d195328, d198412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro18675 (p : Pattern) (selected : d195334 p = 1) : d198418 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d195329 q = 1) : d198413 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d195329, d198413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195329, d198413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18674 q selected
  have h2 (q : Pattern) (selected : d195330 q = 1) : d198414 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d195330, d198414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195330, d198414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d195331 q = 1) : d198415 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d195331, d198415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195331, d198415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d195332 q = 1) : d198416 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d195332, d198416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195332, d198416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d195333 q = 1) : d198417 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d195333, d198417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195333, d198417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195334 q = 1) : d198418 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d195334, d198418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d195334, d198418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18676 (p : Pattern) (selected : d195340 p = 1) : d198424 p = 1 := by
  have h0 (q : Pattern) (selected : d194713 q = 1) : d198253 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194713, d198253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6357 q selected
    | true =>
      simp only [d194713, d198253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18631 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d194852 q = 1) : d198293 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194852, d198293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d194852, d198293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18642 q selected
  have h3 (q : Pattern) (selected : d194853 q = 1) : d198294 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d194853, d198294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d194853, d198294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d195012 q = 1) : d198334 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d195012, d198334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195012, d198334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18653 q selected
  have h5 (q : Pattern) (selected : d195013 q = 1) : d198335 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d195013, d198335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195013, d198335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d195014 q = 1) : d198336 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d195014, d198336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195014, d198336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d195173 q = 1) : d198376 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d195173, d198376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195173, d198376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18664 q selected
  have h8 (q : Pattern) (selected : d195174 q = 1) : d198377 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d195174, d198377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195174, d198377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d195175 q = 1) : d198378 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d195175, d198378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195175, d198378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d195176 q = 1) : d198379 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d195176, d198379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d195176, d198379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d195335 q = 1) : d198419 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d195335, d198419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195335, d198419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18675 q selected
  have h12 (q : Pattern) (selected : d195336 q = 1) : d198420 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d195336, d198420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195336, d198420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d195337 q = 1) : d198421 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d195337, d198421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195337, d198421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d195338 q = 1) : d198422 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d195338, d198422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195338, d198422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d195339 q = 1) : d198423 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d195339, d198423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d195339, d198423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d195340 q = 1) : d198424 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d195340, d198424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d195340, d198424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro18677 (p : Pattern) (selected : d195346 p = 1) : d198430 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d195341 q = 1) : d198425 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d195341, d198425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18676 q selected
    | true =>
      simp only [d195341, d198425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195342 q = 1) : d198426 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d195342, d198426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195342, d198426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d195343 q = 1) : d198427 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d195343, d198427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195343, d198427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195344 q = 1) : d198428 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d195344, d198428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195344, d198428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195345 q = 1) : d198429 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d195345, d198429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195345, d198429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195346 q = 1) : d198430 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d195346, d198430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195346, d198430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18678 (p : Pattern) (selected : d195352 p = 1) : d198436 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d195347 q = 1) : d198431 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d195347, d198431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18677 q selected
    | true =>
      simp only [d195347, d198431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195348 q = 1) : d198432 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d195348, d198432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195348, d198432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d195349 q = 1) : d198433 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d195349, d198433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195349, d198433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195350 q = 1) : d198434 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d195350, d198434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195350, d198434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195351 q = 1) : d198435 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d195351, d198435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195351, d198435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195352 q = 1) : d198436 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d195352, d198436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195352, d198436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18679 (p : Pattern) (selected : d195358 p = 1) : d198442 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d195353 q = 1) : d198437 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d195353, d198437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18678 q selected
    | true =>
      simp only [d195353, d198437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195354 q = 1) : d198438 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d195354, d198438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195354, d198438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d195355 q = 1) : d198439 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d195355, d198439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195355, d198439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195356 q = 1) : d198440 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d195356, d198440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195356, d198440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195357 q = 1) : d198441 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d195357, d198441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195357, d198441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195358 q = 1) : d198442 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d195358, d198442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195358, d198442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18680 (p : Pattern) (selected : d195364 p = 1) : d198448 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d195359 q = 1) : d198443 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d195359, d198443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18679 q selected
    | true =>
      simp only [d195359, d198443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195360 q = 1) : d198444 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d195360, d198444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195360, d198444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d195361 q = 1) : d198445 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d195361, d198445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195361, d198445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195362 q = 1) : d198446 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d195362, d198446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195362, d198446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195363 q = 1) : d198447 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d195363, d198447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195363, d198447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195364 q = 1) : d198448 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d195364, d198448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195364, d198448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18681 (p : Pattern) (selected : d195370 p = 1) : d198454 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d195365 q = 1) : d198449 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d195365, d198449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18680 q selected
    | true =>
      simp only [d195365, d198449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195366 q = 1) : d198450 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d195366, d198450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195366, d198450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d195367 q = 1) : d198451 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d195367, d198451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195367, d198451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195368 q = 1) : d198452 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d195368, d198452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195368, d198452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195369 q = 1) : d198453 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d195369, d198453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195369, d198453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195370 q = 1) : d198454 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d195370, d198454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195370, d198454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18682 (p : Pattern) (selected : d195376 p = 1) : d198460 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d195371 q = 1) : d198455 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d195371, d198455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18681 q selected
    | true =>
      simp only [d195371, d198455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195372 q = 1) : d198456 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d195372, d198456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195372, d198456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d195373 q = 1) : d198457 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d195373, d198457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195373, d198457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195374 q = 1) : d198458 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d195374, d198458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195374, d198458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195375 q = 1) : d198459 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d195375, d198459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195375, d198459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195376 q = 1) : d198460 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d195376, d198460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195376, d198460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18683 (p : Pattern) (selected : d195382 p = 1) : d198466 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d195377 q = 1) : d198461 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d195377, d198461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18682 q selected
    | true =>
      simp only [d195377, d198461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d195378 q = 1) : d198462 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d195378, d198462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d195378, d198462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d195379 q = 1) : d198463 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d195379, d198463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d195379, d198463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d195380 q = 1) : d198464 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d195380, d198464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d195380, d198464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d195381 q = 1) : d198465 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d195381, d198465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d195381, d198465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d195382 q = 1) : d198466 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d195382, d198466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d195382, d198466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18684 (p : Pattern) (selected : d25104 p = 0) : d198470 p = 1 := by
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
  have h3 (q : Pattern) (selected : d9796 q = 0) : d101317 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9796, d101317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9796, d101317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h6 (q : Pattern) (selected : d21 q = 0) : d51873 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d25102 q = 0) : d198468 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25102, d198468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25102, d198468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d25103 q = 0) : d198469 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25103, d198469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d25103, d198469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d22 q = 0) : d51874 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d22, d51874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d22, d51874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d23 q = 0) : d51875 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23, d51875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d23, d51875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d25104 q = 0) : d198470 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25104, d198470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d25104, d198470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro18685 (p : Pattern) (selected : d25110 p = 0) : d198476 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25105 q = 0) : d198471 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25105, d198471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18684 q selected
    | true =>
      simp only [d25105, d198471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d25106 q = 0) : d198472 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25106, d198472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d25106, d198472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d25107 q = 0) : d198473 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25107, d198473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25107, d198473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d25108 q = 0) : d198474 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25108, d198474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25108, d198474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d25 q = 0) : d51877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d26 q = 0) : d51878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d27 q = 0) : d51879 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d28 q = 0) : d51880 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d25109 q = 0) : d198475 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25109, d198475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d25109, d198475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d29 q = 0) : d51881 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, d51881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d29, d51881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d25110 q = 0) : d198476 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25110, d198476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d25110, d198476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro18686 (p : Pattern) (selected : d25116 p = 0) : d198482 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25111 q = 0) : d198477 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25111, d198477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18685 q selected
    | true =>
      simp only [d25111, d198477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro188 q selected
  have h2 (q : Pattern) (selected : d25112 q = 0) : d198478 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25112, d198478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25112, d198478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d25113 q = 0) : d198479 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25113, d198479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25113, d198479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d31 q = 0) : d51883 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro188 q selected
    | true =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d32 q = 0) : d51884 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d33 q = 0) : d51885 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d25114 q = 0) : d198480 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25114, d198480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25114, d198480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d34 q = 0) : d51886 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, d51886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d34, d51886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d25115 q = 0) : d198481 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25115, d198481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d25115, d198481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d25116 q = 0) : d198482 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25116, d198482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d25116, d198482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro18687 (p : Pattern) (selected : d25122 p = 0) : d198488 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25117 q = 0) : d198483 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d198483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18686 q selected
    | true =>
      simp only [d25117, d198483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d25118 q = 0) : d198484 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d198484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25118, d198484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d38 q = 0) : d51890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d25119 q = 0) : d198485 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d198485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25119, d198485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d25120 q = 0) : d198486 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25120, d198486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d25120, d198486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d25121 q = 0) : d198487 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25121, d198487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d25121, d198487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d25122 q = 0) : d198488 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25122, d198488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25122, d198488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro18688 (p : Pattern) (selected : d25128 p = 0) : d198494 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117 q = 0) : d51969 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro202 q selected
    | true =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118 q = 0) : d51970 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d119 q = 0) : d51971 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d120 q = 0) : d51972 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d124 q = 0) : d51976 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro203 q selected
    | true =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d125 q = 0) : d51977 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d126 q = 0) : d51978 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d25123 q = 0) : d198489 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d198489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18687 q selected
    | true =>
      simp only [d25123, d198489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
  have h9 (q : Pattern) (selected : d188 q = 0) : d51895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro213 q selected
    | true =>
      simp only [d188, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d25124 q = 0) : d198490 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25124, d198490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d25124, d198490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d43 q = 0) : d51895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d44 q = 0) : d51896 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d25125 q = 0) : d198491 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25125, d198491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d25125, d198491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d25126 q = 0) : d198492 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25126, d198492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d25126, d198492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d25127 q = 0) : d198493 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25127, d198493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d25127, d198493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d25128 q = 0) : d198494 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25128, d198494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25128, d198494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro18689 (p : Pattern) (selected : d25129 p = 0) : d198495 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25117 q = 0) : d198483 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d198483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18686 q selected
    | true =>
      simp only [d25117, d198483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d25118 q = 0) : d198484 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d198484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25118, d198484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d38 q = 0) : d51890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d25119 q = 0) : d198485 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d198485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25119, d198485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d25120 q = 0) : d198486 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25120, d198486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d25120, d198486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d25121 q = 0) : d198487 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25121, d198487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d25121, d198487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d25129 q = 0) : d198495 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25129, d198495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d25129, d198495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro18690 (p : Pattern) (selected : d25135 p = 0) : d198501 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117 q = 0) : d51969 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro202 q selected
    | true =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118 q = 0) : d51970 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d119 q = 0) : d51971 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d120 q = 0) : d51972 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d124 q = 0) : d51976 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro203 q selected
    | true =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d125 q = 0) : d51977 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d126 q = 0) : d51978 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d25123 q = 0) : d198489 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d198489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18687 q selected
    | true =>
      simp only [d25123, d198489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
  have h9 (q : Pattern) (selected : d188 q = 0) : d51895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro213 q selected
    | true =>
      simp only [d188, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d25124 q = 0) : d198490 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25124, d198490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d25124, d198490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d43 q = 0) : d51895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d44 q = 0) : d51896 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d25125 q = 0) : d198491 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25125, d198491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d25125, d198491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d25126 q = 0) : d198492 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25126, d198492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d25126, d198492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d25127 q = 0) : d198493 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25127, d198493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d25127, d198493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d195 q = 0) : d52015 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, d52015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro215 q selected
    | true =>
      simp only [d195, d52015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d196 q = 0) : d52016 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, d52016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d196, d52016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d197 q = 0) : d52017 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, d52017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d197, d52017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d198 q = 0) : d52018 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, d52018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d198, d52018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d200 q = 0) : d52020 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, d52020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro216 q selected
    | true =>
      simp only [d200, d52020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d201 q = 0) : d52021 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, d52021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d201, d52021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d202 q = 0) : d52022 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, d52022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d202, d52022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d25130 q = 0) : d198496 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25130, d198496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18689 q selected
    | true =>
      simp only [d25130, d198496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro192 q selected
  have h24 (q : Pattern) (selected : d206 q = 0) : d51902 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d206, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro218 q selected
    | true =>
      simp only [d206, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d25131 q = 0) : d198497 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25131, d198497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d25131, d198497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d50 q = 0) : d51902 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro192 q selected
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d51 q = 0) : d51903 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d25132 q = 0) : d198498 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25132, d198498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d25132, d198498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d25133 q = 0) : d198499 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25133, d198499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d25133, d198499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d25134 q = 0) : d198500 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25134, d198500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d25134, d198500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d25135 q = 0) : d198501 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25135, d198501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d25135, d198501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro18691 (p : Pattern) (selected : d25142 p = 0) : d198508 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25130 q = 0) : d198496 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25130, d198496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18689 q selected
    | true =>
      simp only [d25130, d198496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro192 q selected
  have h2 (q : Pattern) (selected : d206 q = 0) : d51902 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d206, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro218 q selected
    | true =>
      simp only [d206, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d25131 q = 0) : d198497 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25131, d198497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d25131, d198497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d50 q = 0) : d51902 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro192 q selected
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d51 q = 0) : d51903 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d25132 q = 0) : d198498 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25132, d198498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25132, d198498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d25140 q = 0) : d198506 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25140, d198506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25140, d198506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d25141 q = 0) : d198507 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25141, d198507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25141, d198507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d25142 q = 0) : d198508 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25142, d198508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25142, d198508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro18692 (p : Pattern) (selected : d25153 p = 0) : d198519 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25148 q = 0) : d198514 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25148, d198514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25148, d198514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18684 q selected
  have h2 (q : Pattern) (selected : d25105 q = 0) : d198471 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25105, d198471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18684 q selected
    | true =>
      simp only [d25105, d198471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d25149 q = 0) : d198515 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25149, d198515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d25149, d198515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d25106 q = 0) : d198472 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25106, d198472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25106, d198472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d25150 q = 0) : d198516 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25150, d198516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25150, d198516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d25151 q = 0) : d198517 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25151, d198517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d25151, d198517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d66 q = 0) : d51918 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
  have h8 (q : Pattern) (selected : d25 q = 0) : d51877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d67 q = 0) : d51919 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d26 q = 0) : d51878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d68 q = 0) : d51920 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d69 q = 0) : d51921 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d25152 q = 0) : d198518 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25152, d198518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d25152, d198518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d70 q = 0) : d51922 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, d51922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d70, d51922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d25153 q = 0) : d198519 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25153, d198519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d25153, d198519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro18693 (p : Pattern) (selected : d25159 p = 0) : d198525 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25154 q = 0) : d198520 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25154, d198520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18692 q selected
    | true =>
      simp only [d25154, d198520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro195 q selected
  have h2 (q : Pattern) (selected : d25155 q = 0) : d198521 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25155, d198521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25155, d198521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d25156 q = 0) : d198522 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25156, d198522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25156, d198522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d72 q = 0) : d51924 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro195 q selected
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d73 q = 0) : d51925 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d74 q = 0) : d51926 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d25157 q = 0) : d198523 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25157, d198523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25157, d198523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d75 q = 0) : d51927 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d25158 q = 0) : d198524 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25158, d198524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d25158, d198524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d25159 q = 0) : d198525 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25159, d198525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d25159, d198525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro18694 (p : Pattern) (selected : d25165 p = 0) : d198531 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25160 q = 0) : d198526 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25160, d198526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18693 q selected
    | true =>
      simp only [d25160, d198526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d25161 q = 0) : d198527 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25161, d198527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25161, d198527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d78 q = 0) : d51930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro196 q selected
    | true =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d79 q = 0) : d51931 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, d51931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d79, d51931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d25162 q = 0) : d198528 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25162, d198528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25162, d198528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d25163 q = 0) : d198529 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25163, d198529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d25163, d198529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d25164 q = 0) : d198530 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25164, d198530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d25164, d198530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d25165 q = 0) : d198531 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25165, d198531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d25165, d198531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro18695 (p : Pattern) (selected : d25171 p = 0) : d198537 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25166 q = 0) : d198532 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25166, d198532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18694 q selected
    | true =>
      simp only [d25166, d198532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro197 q selected
  have h2 (q : Pattern) (selected : d263 q = 0) : d51936 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263, d51936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro227 q selected
    | true =>
      simp only [d263, d51936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d25167 q = 0) : d198533 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25167, d198533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d25167, d198533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d84 q = 0) : d51936 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro197 q selected
    | true =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d85 q = 0) : d51937 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, d51937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d85, d51937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d25168 q = 0) : d198534 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25168, d198534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25168, d198534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d25169 q = 0) : d198535 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25169, d198535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25169, d198535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d25170 q = 0) : d198536 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25170, d198536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25170, d198536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d25171 q = 0) : d198537 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25171, d198537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25171, d198537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro18696 (p : Pattern) (selected : d25177 p = 0) : d198543 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105 q = 0) : d51957 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, d51957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105, d51957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro200 q selected
  have h2 (q : Pattern) (selected : d106 q = 0) : d51958 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, d51958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d106, d51958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d112 q = 0) : d51964 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d51964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro200 q selected
    | true =>
      simp only [d112, d51964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro201 q selected
  have h4 (q : Pattern) (selected : d113 q = 0) : d51965 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d51965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d113, d51965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d114 q = 0) : d51966 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, d51966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d114, d51966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d25136 q = 0) : d198502 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25136, d198502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18688 q selected
    | true =>
      simp only [d25136, d198502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18690 q selected
  have h7 (q : Pattern) (selected : d214 q = 0) : d52032 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro220 q selected
    | true =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d25137 q = 0) : d198503 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25137, d198503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d25137, d198503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d25138 q = 0) : d198504 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d25138, d198504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d25138, d198504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d25139 q = 0) : d198505 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d25139, d198505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d25139, d198505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d25143 q = 0) : d198509 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25143, d198509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25143, d198509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18691 q selected
  have h12 (q : Pattern) (selected : d25144 q = 0) : d198510 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25144, d198510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d25144, d198510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d25145 q = 0) : d198511 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d25145, d198511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d25145, d198511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d25146 q = 0) : d198512 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d25146, d198512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d25146, d198512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d25147 q = 0) : d198513 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d25147, d198513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d25147, d198513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d25172 q = 0) : d198538 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25172, d198538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25172, d198538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18695 q selected
  have h17 (q : Pattern) (selected : d25173 q = 0) : d198539 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25173, d198539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d25173, d198539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d25174 q = 0) : d198540 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d25174, d198540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d25174, d198540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d25175 q = 0) : d198541 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d25175, d198541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d25175, d198541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d25176 q = 0) : d198542 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d25176, d198542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d25176, d198542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d25177 q = 0) : d198543 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d25177, d198543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d25177, d198543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro18697 (p : Pattern) (selected : d25187 p = 0) : d198553 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25123 q = 0) : d198489 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d198489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18687 q selected
    | true =>
      simp only [d25123, d198489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
  have h2 (q : Pattern) (selected : d25183 q = 0) : d198549 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25183, d198549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25183, d198549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d25184 q = 0) : d198550 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25184, d198550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25184, d198550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d25185 q = 0) : d198551 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25185, d198551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25185, d198551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d25186 q = 0) : d198552 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25186, d198552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25186, d198552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d25187 q = 0) : d198553 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25187, d198553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25187, d198553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18698 (p : Pattern) (selected : d25194 p = 0) : d198560 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25123 q = 0) : d198489 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d198489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18687 q selected
    | true =>
      simp only [d25123, d198489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
  have h2 (q : Pattern) (selected : d25183 q = 0) : d198549 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25183, d198549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25183, d198549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d25184 q = 0) : d198550 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25184, d198550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25184, d198550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d25185 q = 0) : d198551 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25185, d198551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25185, d198551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d25186 q = 0) : d198552 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25186, d198552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25186, d198552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d25130 q = 0) : d198496 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25130, d198496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18689 q selected
    | true =>
      simp only [d25130, d198496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro192 q selected
  have h7 (q : Pattern) (selected : d25190 q = 0) : d198556 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25190, d198556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25190, d198556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d25191 q = 0) : d198557 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25191, d198557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d25191, d198557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d25192 q = 0) : d198558 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25192, d198558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25192, d198558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d25193 q = 0) : d198559 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25193, d198559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25193, d198559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d25194 q = 0) : d198560 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25194, d198560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d25194, d198560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro18699 (p : Pattern) (selected : d25199 p = 0) : d198565 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25117 q = 0) : d198483 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d198483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18686 q selected
    | true =>
      simp only [d25117, d198483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d25118 q = 0) : d198484 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d198484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25118, d198484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d38 q = 0) : d51890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d25119 q = 0) : d198485 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d198485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25119, d198485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d25120 q = 0) : d198486 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25120, d198486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d25120, d198486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d25198 q = 0) : d198564 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25198, d198564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25198, d198564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d25199 q = 0) : d198565 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25199, d198565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25199, d198565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro18700 (p : Pattern) (selected : d25206 p = 0) : d198572 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25117 q = 0) : d198483 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d198483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18686 q selected
    | true =>
      simp only [d25117, d198483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d25118 q = 0) : d198484 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d198484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25118, d198484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d38 q = 0) : d51890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d25119 q = 0) : d198485 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d198485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25119, d198485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d25204 q = 0) : d198570 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25204, d198570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25204, d198570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d25205 q = 0) : d198571 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25205, d198571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d25205, d198571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d25206 q = 0) : d198572 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25206, d198572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25206, d198572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro18701 (p : Pattern) (selected : d25213 p = 0) : d198579 p = 1 := by
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
  have h3 (q : Pattern) (selected : d25210 q = 0) : d198576 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25210, d198576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25210, d198576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h6 (q : Pattern) (selected : d9796 q = 0) : d101317 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9796, d101317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9796, d101317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d25211 q = 0) : d198577 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25211, d198577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25211, d198577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d25212 q = 0) : d198578 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25212, d198578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d25212, d198578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d19 q = 0) : d51871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d20 q = 0) : d51872 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d21 q = 0) : d51873 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d25102 q = 0) : d198468 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25102, d198468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d25102, d198468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d25103 q = 0) : d198469 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25103, d198469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d25103, d198469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d25213 q = 0) : d198579 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25213, d198579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d25213, d198579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro18702 (p : Pattern) (selected : d25221 p = 0) : d198587 p = 1 := by
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
  have h3 (q : Pattern) (selected : d9796 q = 0) : d101317 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9796, d101317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9796, d101317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d25219 q = 0) : d198585 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25219, d198585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25219, d198585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d25220 q = 0) : d198586 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25220, d198586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d25220, d198586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d19 q = 0) : d51871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro186 q selected
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20 q = 0) : d51872 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d21 q = 0) : d51873 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d22 q = 0) : d51874 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d22, d51874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d22, d51874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d23 q = 0) : d51875 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23, d51875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d23, d51875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d25221 q = 0) : d198587 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25221, d198587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d25221, d198587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro18703 (p : Pattern) (selected : d25227 p = 0) : d198593 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25214 q = 0) : d198580 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25214, d198580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18701 q selected
    | true =>
      simp only [d25214, d198580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d25215 q = 0) : d198581 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25215, d198581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d25215, d198581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d25216 q = 0) : d198582 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25216, d198582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25216, d198582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d25217 q = 0) : d198583 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25217, d198583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25217, d198583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d25105 q = 0) : d198471 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25105, d198471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18684 q selected
    | true =>
      simp only [d25105, d198471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d25106 q = 0) : d198472 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25106, d198472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d25106, d198472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d25107 q = 0) : d198473 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25107, d198473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25107, d198473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d25108 q = 0) : d198474 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25108, d198474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d25108, d198474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d25218 q = 0) : d198584 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25218, d198584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d25218, d198584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d25222 q = 0) : d198588 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25222, d198588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18702 q selected
    | true =>
      simp only [d25222, d198588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d25223 q = 0) : d198589 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25223, d198589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d25223, d198589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d25224 q = 0) : d198590 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25224, d198590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25224, d198590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d25225 q = 0) : d198591 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25225, d198591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d25225, d198591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d25 q = 0) : d51877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d26 q = 0) : d51878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d27 q = 0) : d51879 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d28 q = 0) : d51880 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d25226 q = 0) : d198592 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25226, d198592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d25226, d198592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d25227 q = 0) : d198593 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25227, d198593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d25227, d198593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro18704 (p : Pattern) (selected : d25233 p = 0) : d198599 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25228 q = 0) : d198594 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25228, d198594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18703 q selected
    | true =>
      simp only [d25228, d198594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18685 q selected
  have h2 (q : Pattern) (selected : d25229 q = 0) : d198595 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25229, d198595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25229, d198595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d25230 q = 0) : d198596 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25230, d198596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25230, d198596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d25111 q = 0) : d198477 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25111, d198477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18685 q selected
    | true =>
      simp only [d25111, d198477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro188 q selected
  have h5 (q : Pattern) (selected : d25112 q = 0) : d198478 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25112, d198478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25112, d198478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d25113 q = 0) : d198479 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25113, d198479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25113, d198479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d25231 q = 0) : d198597 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25231, d198597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25231, d198597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d31 q = 0) : d51883 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro188 q selected
    | true =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d32 q = 0) : d51884 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d33 q = 0) : d51885 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d25114 q = 0) : d198480 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25114, d198480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d25114, d198480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d25232 q = 0) : d198598 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25232, d198598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d25232, d198598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d25233 q = 0) : d198599 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25233, d198599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d25233, d198599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro18705 (p : Pattern) (selected : d25239 p = 0) : d198605 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25234 q = 0) : d198600 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25234, d198600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18704 q selected
    | true =>
      simp only [d25234, d198600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d25235 q = 0) : d198601 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25235, d198601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25235, d198601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d25117 q = 0) : d198483 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d198483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18686 q selected
    | true =>
      simp only [d25117, d198483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d25118 q = 0) : d198484 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d198484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25118, d198484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d25236 q = 0) : d198602 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25236, d198602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25236, d198602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d25237 q = 0) : d198603 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25237, d198603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d25237, d198603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d25238 q = 0) : d198604 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25238, d198604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d25238, d198604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d25239 q = 0) : d198605 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25239, d198605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25239, d198605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro18706 (p : Pattern) (selected : d25243 p = 0) : d198470 p = 1 := by
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
  have h3 (q : Pattern) (selected : d9914 q = 0) : d101317 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9914, d101317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9914, d101317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h6 (q : Pattern) (selected : d166 q = 0) : d51873 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d166, d51873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d166, d51873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d25241 q = 0) : d198468 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25241, d198468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25241, d198468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d25242 q = 0) : d198469 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25242, d198469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d25242, d198469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d167 q = 0) : d51874 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d167, d51874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d167, d51874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d168 q = 0) : d51875 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d168, d51875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d168, d51875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d25243 q = 0) : d198470 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25243, d198470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d25243, d198470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro18707 (p : Pattern) (selected : d25249 p = 0) : d198476 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25244 q = 0) : d198471 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25244, d198471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18706 q selected
    | true =>
      simp only [d25244, d198471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d25245 q = 0) : d198472 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25245, d198472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d25245, d198472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d25246 q = 0) : d198473 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25246, d198473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25246, d198473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d25247 q = 0) : d198474 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25247, d198474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25247, d198474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d170 q = 0) : d51877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro210 q selected
    | true =>
      simp only [d170, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d171 q = 0) : d51878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d171, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d171, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d172 q = 0) : d51879 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d172, d51879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172, d51879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d173 q = 0) : d51880 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173, d51880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d173, d51880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d25248 q = 0) : d198475 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25248, d198475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d25248, d198475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d174 q = 0) : d51881 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174, d51881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d174, d51881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d25249 q = 0) : d198476 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25249, d198476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d25249, d198476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro18708 (p : Pattern) (selected : d25255 p = 0) : d198482 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25250 q = 0) : d198477 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25250, d198477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18707 q selected
    | true =>
      simp only [d25250, d198477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro211 q selected
  have h2 (q : Pattern) (selected : d25251 q = 0) : d198478 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25251, d198478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25251, d198478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d25252 q = 0) : d198479 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25252, d198479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25252, d198479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176 q = 0) : d51883 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176, d51883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro211 q selected
    | true =>
      simp only [d176, d51883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d177 q = 0) : d51884 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177, d51884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177, d51884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d178 q = 0) : d51885 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d178, d51885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d178, d51885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d25253 q = 0) : d198480 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25253, d198480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25253, d198480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d179 q = 0) : d51886 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d179, d51886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d179, d51886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d25254 q = 0) : d198481 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25254, d198481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d25254, d198481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d25255 q = 0) : d198482 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25255, d198482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d25255, d198482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro18709 (p : Pattern) (selected : d25261 p = 0) : d198488 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25256 q = 0) : d198483 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25256, d198483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18708 q selected
    | true =>
      simp only [d25256, d198483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d25257 q = 0) : d198484 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25257, d198484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25257, d198484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro212 q selected
    | true =>
      simp only [d182, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d183 q = 0) : d51890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d183, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d25258 q = 0) : d198485 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25258, d198485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25258, d198485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d25259 q = 0) : d198486 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25259, d198486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d25259, d198486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d25260 q = 0) : d198487 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25260, d198487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d25260, d198487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d25261 q = 0) : d198488 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25261, d198488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25261, d198488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro18710 (p : Pattern) (selected : d25267 p = 0) : d198611 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25117 q = 0) : d198483 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d198483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18686 q selected
    | true =>
      simp only [d25117, d198483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d25118 q = 0) : d198484 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d198484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25118, d198484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d25264 q = 0) : d198608 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25264, d198608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25264, d198608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d25265 q = 0) : d198609 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25265, d198609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25265, d198609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d25266 q = 0) : d198610 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25266, d198610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d25266, d198610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d25267 q = 0) : d198611 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25267, d198611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25267, d198611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18711 (p : Pattern) (selected : d25273 p = 0) : d198617 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25200 q = 0) : d198566 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25200, d198566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18699 q selected
    | true =>
      simp only [d25200, d198566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro202 q selected
  have h2 (q : Pattern) (selected : d25201 q = 0) : d198567 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25201, d198567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25201, d198567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d25202 q = 0) : d198568 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25202, d198568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25202, d198568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d25203 q = 0) : d198569 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25203, d198569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25203, d198569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d25207 q = 0) : d198573 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25207, d198573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18700 q selected
    | true =>
      simp only [d25207, d198573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro203 q selected
  have h6 (q : Pattern) (selected : d25208 q = 0) : d198574 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25208, d198574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25208, d198574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d25209 q = 0) : d198575 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25209, d198575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d25209, d198575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d25240 q = 0) : d198606 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25240, d198606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18705 q selected
    | true =>
      simp only [d25240, d198606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18687 q selected
  have h9 (q : Pattern) (selected : d25262 q = 0) : d198489 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25262, d198489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18709 q selected
    | true =>
      simp only [d25262, d198489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro213 q selected
  have h10 (q : Pattern) (selected : d25263 q = 0) : d198607 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25263, d198607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d25263, d198607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d25268 q = 0) : d198612 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25268, d198612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18710 q selected
    | true =>
      simp only [d25268, d198612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d25269 q = 0) : d198613 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25269, d198613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d25269, d198613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d25270 q = 0) : d198614 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25270, d198614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d25270, d198614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d25271 q = 0) : d198615 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25271, d198615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d25271, d198615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d25272 q = 0) : d198616 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25272, d198616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d25272, d198616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d25273 q = 0) : d198617 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25273, d198617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25273, d198617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro18712 (p : Pattern) (selected : d25274 p = 0) : d198618 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25117 q = 0) : d198483 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d198483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18686 q selected
    | true =>
      simp only [d25117, d198483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d25118 q = 0) : d198484 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d198484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25118, d198484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d38 q = 0) : d51890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d25119 q = 0) : d198485 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d198485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25119, d198485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d25120 q = 0) : d198486 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25120, d198486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d25120, d198486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d25198 q = 0) : d198564 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25198, d198564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25198, d198564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d25274 q = 0) : d198618 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25274, d198618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d25274, d198618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro18713 (p : Pattern) (selected : d25279 p = 0) : d198623 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25117 q = 0) : d198483 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d198483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18686 q selected
    | true =>
      simp only [d25117, d198483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d25118 q = 0) : d198484 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d198484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25118, d198484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d38 q = 0) : d51890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d25119 q = 0) : d198485 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d198485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25119, d198485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d25204 q = 0) : d198570 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25204, d198570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25204, d198570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d25205 q = 0) : d198571 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25205, d198571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d25205, d198571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d25279 q = 0) : d198623 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25279, d198623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d25279, d198623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro18714 (p : Pattern) (selected : d25283 p = 0) : d198627 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25234 q = 0) : d198600 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25234, d198600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18704 q selected
    | true =>
      simp only [d25234, d198600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d25235 q = 0) : d198601 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25235, d198601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25235, d198601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d25117 q = 0) : d198483 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d198483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18686 q selected
    | true =>
      simp only [d25117, d198483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d25118 q = 0) : d198484 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d198484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25118, d198484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d25236 q = 0) : d198602 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25236, d198602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25236, d198602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d25237 q = 0) : d198603 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25237, d198603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d25237, d198603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d25238 q = 0) : d198604 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25238, d198604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d25238, d198604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d25283 q = 0) : d198627 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25283, d198627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d25283, d198627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro18715 (p : Pattern) (selected : d25285 p = 0) : d198495 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25256 q = 0) : d198483 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25256, d198483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18708 q selected
    | true =>
      simp only [d25256, d198483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d25257 q = 0) : d198484 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25257, d198484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25257, d198484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro212 q selected
    | true =>
      simp only [d182, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d183 q = 0) : d51890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d183, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d25258 q = 0) : d198485 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25258, d198485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25258, d198485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d25259 q = 0) : d198486 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25259, d198486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d25259, d198486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d25260 q = 0) : d198487 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25260, d198487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d25260, d198487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d25285 q = 0) : d198495 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25285, d198495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d25285, d198495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro18716 (p : Pattern) (selected : d25288 p = 0) : d198630 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25117 q = 0) : d198483 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d198483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18686 q selected
    | true =>
      simp only [d25117, d198483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d25118 q = 0) : d198484 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d198484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25118, d198484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d25264 q = 0) : d198608 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25264, d198608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25264, d198608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d25265 q = 0) : d198609 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25265, d198609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25265, d198609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d25266 q = 0) : d198610 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25266, d198610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d25266, d198610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d25288 q = 0) : d198630 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25288, d198630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d25288, d198630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18717 (p : Pattern) (selected : d25294 p = 0) : d198636 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25200 q = 0) : d198566 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25200, d198566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18699 q selected
    | true =>
      simp only [d25200, d198566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro202 q selected
  have h2 (q : Pattern) (selected : d25201 q = 0) : d198567 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25201, d198567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25201, d198567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d25202 q = 0) : d198568 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25202, d198568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25202, d198568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d25203 q = 0) : d198569 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25203, d198569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25203, d198569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d25207 q = 0) : d198573 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25207, d198573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18700 q selected
    | true =>
      simp only [d25207, d198573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro203 q selected
  have h6 (q : Pattern) (selected : d25208 q = 0) : d198574 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25208, d198574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25208, d198574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d25209 q = 0) : d198575 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25209, d198575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d25209, d198575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d25240 q = 0) : d198606 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25240, d198606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18705 q selected
    | true =>
      simp only [d25240, d198606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18687 q selected
  have h9 (q : Pattern) (selected : d25262 q = 0) : d198489 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25262, d198489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18709 q selected
    | true =>
      simp only [d25262, d198489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro213 q selected
  have h10 (q : Pattern) (selected : d25263 q = 0) : d198607 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25263, d198607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d25263, d198607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d25268 q = 0) : d198612 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25268, d198612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18710 q selected
    | true =>
      simp only [d25268, d198612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d25269 q = 0) : d198613 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25269, d198613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d25269, d198613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d25270 q = 0) : d198614 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25270, d198614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d25270, d198614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d25271 q = 0) : d198615 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25271, d198615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d25271, d198615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d25272 q = 0) : d198616 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25272, d198616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d25272, d198616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d25275 q = 0) : d198619 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25275, d198619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18712 q selected
    | true =>
      simp only [d25275, d198619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro215 q selected
  have h17 (q : Pattern) (selected : d25276 q = 0) : d198620 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25276, d198620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25276, d198620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d25277 q = 0) : d198621 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25277, d198621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d25277, d198621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d25278 q = 0) : d198622 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25278, d198622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25278, d198622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d25280 q = 0) : d198624 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25280, d198624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18713 q selected
    | true =>
      simp only [d25280, d198624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro216 q selected
  have h21 (q : Pattern) (selected : d25281 q = 0) : d198625 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25281, d198625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25281, d198625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d25282 q = 0) : d198626 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25282, d198626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d25282, d198626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d25284 q = 0) : d198628 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25284, d198628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18714 q selected
    | true =>
      simp only [d25284, d198628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18689 q selected
  have h24 (q : Pattern) (selected : d25286 q = 0) : d198496 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25286, d198496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18715 q selected
    | true =>
      simp only [d25286, d198496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro218 q selected
  have h25 (q : Pattern) (selected : d25287 q = 0) : d198629 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25287, d198629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d25287, d198629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d25289 q = 0) : d198631 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25289, d198631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18716 q selected
    | true =>
      simp only [d25289, d198631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d25290 q = 0) : d198632 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25290, d198632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d25290, d198632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d25291 q = 0) : d198633 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25291, d198633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d25291, d198633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d25292 q = 0) : d198634 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25292, d198634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d25292, d198634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d25293 q = 0) : d198635 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25293, d198635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d25293, d198635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d25294 q = 0) : d198636 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25294, d198636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d25294, d198636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro18718 (p : Pattern) (selected : d25296 p = 0) : d198638 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25123 q = 0) : d198489 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d198489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18687 q selected
    | true =>
      simp only [d25123, d198489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
  have h2 (q : Pattern) (selected : d25183 q = 0) : d198549 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25183, d198549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25183, d198549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d25184 q = 0) : d198550 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25184, d198550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25184, d198550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d25185 q = 0) : d198551 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25185, d198551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25185, d198551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d25186 q = 0) : d198552 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25186, d198552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25186, d198552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d43 q = 0) : d51895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d100 q = 0) : d51952 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d101 q = 0) : d51953 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d102 q = 0) : d51954 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d51954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102, d51954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d103 q = 0) : d51955 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d51955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103, d51955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d25296 q = 0) : d198638 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25296, d198638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d25296, d198638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro18719 (p : Pattern) (selected : d25303 p = 0) : d198645 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25284 q = 0) : d198628 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25284, d198628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18714 q selected
    | true =>
      simp only [d25284, d198628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18689 q selected
  have h2 (q : Pattern) (selected : d25286 q = 0) : d198496 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25286, d198496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18715 q selected
    | true =>
      simp only [d25286, d198496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro218 q selected
  have h3 (q : Pattern) (selected : d25287 q = 0) : d198629 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25287, d198629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d25287, d198629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d25289 q = 0) : d198631 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25289, d198631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18716 q selected
    | true =>
      simp only [d25289, d198631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d25290 q = 0) : d198632 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25290, d198632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d25290, d198632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d25291 q = 0) : d198633 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25291, d198633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25291, d198633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d25301 q = 0) : d198643 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25301, d198643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25301, d198643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d25302 q = 0) : d198644 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25302, d198644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25302, d198644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d25303 q = 0) : d198645 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25303, d198645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25303, d198645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro18720 (p : Pattern) (selected : d25319 p = 0) : d198661 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25309 q = 0) : d198651 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25309, d198651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25309, d198651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18701 q selected
  have h2 (q : Pattern) (selected : d25214 q = 0) : d198580 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25214, d198580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18701 q selected
    | true =>
      simp only [d25214, d198580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d25310 q = 0) : d198652 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25310, d198652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d25310, d198652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d25215 q = 0) : d198581 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25215, d198581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25215, d198581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d25311 q = 0) : d198653 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25311, d198653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25311, d198653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d25312 q = 0) : d198654 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25312, d198654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d25312, d198654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d25148 q = 0) : d198514 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25148, d198514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25148, d198514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18684 q selected
  have h8 (q : Pattern) (selected : d25105 q = 0) : d198471 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25105, d198471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18684 q selected
    | true =>
      simp only [d25105, d198471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d25149 q = 0) : d198515 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25149, d198515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d25149, d198515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d25106 q = 0) : d198472 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25106, d198472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d25106, d198472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d25150 q = 0) : d198516 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25150, d198516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d25150, d198516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d25151 q = 0) : d198517 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25151, d198517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d25151, d198517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d25313 q = 0) : d198655 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25313, d198655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d25313, d198655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d25314 q = 0) : d198656 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25314, d198656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25314, d198656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18702 q selected
  have h15 (q : Pattern) (selected : d25222 q = 0) : d198588 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25222, d198588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18702 q selected
    | true =>
      simp only [d25222, d198588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d25315 q = 0) : d198657 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25315, d198657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d25315, d198657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d25223 q = 0) : d198589 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25223, d198589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d25223, d198589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d25316 q = 0) : d198658 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25316, d198658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d25316, d198658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d25317 q = 0) : d198659 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25317, d198659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d25317, d198659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d66 q = 0) : d51918 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
  have h21 (q : Pattern) (selected : d25 q = 0) : d51877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d67 q = 0) : d51919 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d26 q = 0) : d51878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d68 q = 0) : d51920 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d69 q = 0) : d51921 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d25318 q = 0) : d198660 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25318, d198660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d25318, d198660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d25319 q = 0) : d198661 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25319, d198661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d25319, d198661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro18721 (p : Pattern) (selected : d25325 p = 0) : d198667 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25320 q = 0) : d198662 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25320, d198662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18720 q selected
    | true =>
      simp only [d25320, d198662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18692 q selected
  have h2 (q : Pattern) (selected : d25321 q = 0) : d198663 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25321, d198663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25321, d198663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d25322 q = 0) : d198664 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25322, d198664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25322, d198664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d25154 q = 0) : d198520 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25154, d198520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18692 q selected
    | true =>
      simp only [d25154, d198520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro195 q selected
  have h5 (q : Pattern) (selected : d25155 q = 0) : d198521 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25155, d198521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25155, d198521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d25156 q = 0) : d198522 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25156, d198522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25156, d198522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d25323 q = 0) : d198665 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25323, d198665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25323, d198665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d72 q = 0) : d51924 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro195 q selected
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d73 q = 0) : d51925 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d74 q = 0) : d51926 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d25157 q = 0) : d198523 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25157, d198523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d25157, d198523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d25324 q = 0) : d198666 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25324, d198666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d25324, d198666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d25325 q = 0) : d198667 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25325, d198667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d25325, d198667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro18722 (p : Pattern) (selected : d25331 p = 0) : d198673 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25326 q = 0) : d198668 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25326, d198668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18721 q selected
    | true =>
      simp only [d25326, d198668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d25327 q = 0) : d198669 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25327, d198669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25327, d198669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d25160 q = 0) : d198526 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25160, d198526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18693 q selected
    | true =>
      simp only [d25160, d198526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d25161 q = 0) : d198527 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25161, d198527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25161, d198527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d25328 q = 0) : d198670 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25328, d198670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25328, d198670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d25329 q = 0) : d198671 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25329, d198671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d25329, d198671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d25330 q = 0) : d198672 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25330, d198672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d25330, d198672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d25331 q = 0) : d198673 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25331, d198673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d25331, d198673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro18723 (p : Pattern) (selected : d25338 p = 0) : d198519 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25333 q = 0) : d198514 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25333, d198514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25333, d198514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18706 q selected
  have h2 (q : Pattern) (selected : d25244 q = 0) : d198471 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25244, d198471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18706 q selected
    | true =>
      simp only [d25244, d198471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d25334 q = 0) : d198515 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25334, d198515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d25334, d198515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d25245 q = 0) : d198472 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25245, d198472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25245, d198472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d25335 q = 0) : d198516 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25335, d198516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25335, d198516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d25336 q = 0) : d198517 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25336, d198517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d25336, d198517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d245 q = 0) : d51918 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d245, d51918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d245, d51918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro210 q selected
  have h8 (q : Pattern) (selected : d170 q = 0) : d51877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro210 q selected
    | true =>
      simp only [d170, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d246 q = 0) : d51919 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246, d51919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246, d51919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d171 q = 0) : d51878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d171, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d171, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d247 q = 0) : d51920 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247, d51920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d247, d51920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d248 q = 0) : d51921 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d248, d51921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d248, d51921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d25337 q = 0) : d198518 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25337, d198518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d25337, d198518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d249 q = 0) : d51922 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d249, d51922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d249, d51922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d25338 q = 0) : d198519 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25338, d198519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d25338, d198519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro18724 (p : Pattern) (selected : d25344 p = 0) : d198525 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25339 q = 0) : d198520 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25339, d198520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18723 q selected
    | true =>
      simp only [d25339, d198520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro225 q selected
  have h2 (q : Pattern) (selected : d25340 q = 0) : d198521 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25340, d198521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25340, d198521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d25341 q = 0) : d198522 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25341, d198522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25341, d198522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d251 q = 0) : d51924 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d251, d51924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro225 q selected
    | true =>
      simp only [d251, d51924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d252 q = 0) : d51925 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d252, d51925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d252, d51925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d253 q = 0) : d51926 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d253, d51926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253, d51926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d25342 q = 0) : d198523 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25342, d198523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25342, d198523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d254 q = 0) : d51927 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d254, d51927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254, d51927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d25343 q = 0) : d198524 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25343, d198524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d25343, d198524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d25344 q = 0) : d198525 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25344, d198525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d25344, d198525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro18725 (p : Pattern) (selected : d25350 p = 0) : d198531 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25345 q = 0) : d198526 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25345, d198526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18724 q selected
    | true =>
      simp only [d25345, d198526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d25346 q = 0) : d198527 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25346, d198527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25346, d198527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d257 q = 0) : d51930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d257, d51930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro226 q selected
    | true =>
      simp only [d257, d51930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d258 q = 0) : d51931 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d258, d51931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d258, d51931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d25347 q = 0) : d198528 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25347, d198528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25347, d198528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d25348 q = 0) : d198529 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25348, d198529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d25348, d198529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d25349 q = 0) : d198530 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25349, d198530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d25349, d198530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d25350 q = 0) : d198531 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25350, d198531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d25350, d198531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro18726 (p : Pattern) (selected : d25356 p = 0) : d198679 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25160 q = 0) : d198526 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25160, d198526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18693 q selected
    | true =>
      simp only [d25160, d198526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d25161 q = 0) : d198527 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25161, d198527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25161, d198527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d25353 q = 0) : d198676 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25353, d198676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25353, d198676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d25354 q = 0) : d198677 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25354, d198677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25354, d198677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d25355 q = 0) : d198678 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25355, d198678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d25355, d198678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d25356 q = 0) : d198679 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25356, d198679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d25356, d198679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18727 (p : Pattern) (selected : d25362 p = 0) : d198685 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25332 q = 0) : d198674 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25332, d198674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18722 q selected
    | true =>
      simp only [d25332, d198674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18694 q selected
  have h2 (q : Pattern) (selected : d25351 q = 0) : d198532 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25351, d198532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18725 q selected
    | true =>
      simp only [d25351, d198532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro227 q selected
  have h3 (q : Pattern) (selected : d25352 q = 0) : d198675 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25352, d198675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d25352, d198675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d25357 q = 0) : d198680 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25357, d198680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18726 q selected
    | true =>
      simp only [d25357, d198680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d25358 q = 0) : d198681 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25358, d198681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d25358, d198681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d25359 q = 0) : d198682 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25359, d198682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25359, d198682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d25360 q = 0) : d198683 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25360, d198683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25360, d198683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d25361 q = 0) : d198684 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25361, d198684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25361, d198684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d25362 q = 0) : d198685 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25362, d198685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25362, d198685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro18728 (p : Pattern) (selected : d25368 p = 0) : d198691 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25188 q = 0) : d198554 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25188, d198554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25188, d198554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18697 q selected
  have h2 (q : Pattern) (selected : d25189 q = 0) : d198555 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25189, d198555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d25189, d198555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d25195 q = 0) : d198561 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25195, d198561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18697 q selected
    | true =>
      simp only [d25195, d198561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18698 q selected
  have h4 (q : Pattern) (selected : d25196 q = 0) : d198562 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25196, d198562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25196, d198562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d25197 q = 0) : d198563 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d25197, d198563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25197, d198563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d25295 q = 0) : d198637 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25295, d198637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18711 q selected
    | true =>
      simp only [d25295, d198637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18717 q selected
  have h7 (q : Pattern) (selected : d25297 q = 0) : d198639 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25297, d198639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18718 q selected
    | true =>
      simp only [d25297, d198639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro201 q selected
  have h8 (q : Pattern) (selected : d25298 q = 0) : d198640 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25298, d198640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d25298, d198640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d25299 q = 0) : d198641 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d25299, d198641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d25299, d198641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d25300 q = 0) : d198642 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d25300, d198642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d25300, d198642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d25304 q = 0) : d198646 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25304, d198646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25304, d198646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18719 q selected
  have h12 (q : Pattern) (selected : d407 q = 0) : d52173 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d52173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d407, d52173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro252 q selected
  have h13 (q : Pattern) (selected : d25305 q = 0) : d198647 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25305, d198647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d25305, d198647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d25306 q = 0) : d198648 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d25306, d198648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d25306, d198648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d25307 q = 0) : d198649 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d25307, d198649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d25307, d198649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d25308 q = 0) : d198650 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d25308, d198650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d25308, d198650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d25363 q = 0) : d198686 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25363, d198686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25363, d198686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18727 q selected
  have h18 (q : Pattern) (selected : d463 q = 0) : d52210 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d52210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d463, d52210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro260 q selected
  have h19 (q : Pattern) (selected : d25364 q = 0) : d198687 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25364, d198687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d25364, d198687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d25365 q = 0) : d198688 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d25365, d198688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d25365, d198688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d25366 q = 0) : d198689 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d25366, d198689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d25366, d198689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d25367 q = 0) : d198690 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d25367, d198690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d25367, d198690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d25368 q = 0) : d198691 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d25368, d198691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d25368, d198691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro18729 (p : Pattern) (selected : d25374 p = 0) : d198697 p = 1 := by
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
  have h5 (q : Pattern) (selected : d25178 q = 0) : d198544 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d25178, d198544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25178, d198544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18696 q selected
  have h6 (q : Pattern) (selected : d25179 q = 0) : d198545 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d25179, d198545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25179, d198545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d25180 q = 0) : d198546 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d25180, d198546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25180, d198546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d25181 q = 0) : d198547 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d25181, d198547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25181, d198547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d25182 q = 0) : d198548 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d25182, d198548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d25182, d198548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d25369 q = 0) : d198692 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d25369, d198692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25369, d198692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18728 q selected
  have h11 (q : Pattern) (selected : d25370 q = 0) : d198693 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d25370, d198693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25370, d198693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d25371 q = 0) : d198694 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d25371, d198694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25371, d198694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d25372 q = 0) : d198695 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d25372, d198695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25372, d198695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d25373 q = 0) : d198696 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d25373, d198696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25373, d198696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d25374 q = 0) : d198697 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d25374, d198697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d25374, d198697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro18730 (p : Pattern) (selected : d25377 p = 0) : d198700 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25228 q = 0) : d198594 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25228, d198594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18703 q selected
    | true =>
      simp only [d25228, d198594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18685 q selected
  have h2 (q : Pattern) (selected : d25229 q = 0) : d198595 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25229, d198595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25229, d198595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d25230 q = 0) : d198596 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25230, d198596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25230, d198596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d25111 q = 0) : d198477 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25111, d198477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18685 q selected
    | true =>
      simp only [d25111, d198477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro188 q selected
  have h5 (q : Pattern) (selected : d25112 q = 0) : d198478 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25112, d198478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25112, d198478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d25113 q = 0) : d198479 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25113, d198479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25113, d198479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d25231 q = 0) : d198597 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25231, d198597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25231, d198597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d25375 q = 0) : d198698 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25375, d198698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d25375, d198698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d25376 q = 0) : d198699 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25376, d198699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d25376, d198699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d25377 q = 0) : d198700 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25377, d198700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d25377, d198700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro18731 (p : Pattern) (selected : d25381 p = 0) : d198704 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25111 q = 0) : d198477 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25111, d198477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18685 q selected
    | true =>
      simp only [d25111, d198477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro188 q selected
  have h2 (q : Pattern) (selected : d25112 q = 0) : d198478 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25112, d198478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25112, d198478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d25113 q = 0) : d198479 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25113, d198479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25113, d198479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d25375 q = 0) : d198698 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25375, d198698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25375, d198698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d25380 q = 0) : d198703 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25380, d198703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d25380, d198703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d25381 q = 0) : d198704 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25381, d198704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d25381, d198704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18732 (p : Pattern) (selected : d25387 p = 0) : d198710 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25378 q = 0) : d198701 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d198701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18730 q selected
    | true =>
      simp only [d25378, d198701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d25379 q = 0) : d198702 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d198702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25379, d198702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d25382 q = 0) : d198705 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d198705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18731 q selected
    | true =>
      simp only [d25382, d198705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d25383 q = 0) : d198706 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d198706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25383, d198706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d25384 q = 0) : d198707 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25384, d198707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25384, d198707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d25385 q = 0) : d198708 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25385, d198708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d25385, d198708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d25386 q = 0) : d198709 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25386, d198709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d25386, d198709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d25387 q = 0) : d198710 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25387, d198710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25387, d198710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro18733 (p : Pattern) (selected : d25391 p = 0) : d198714 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25382 q = 0) : d198705 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d198705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18731 q selected
    | true =>
      simp only [d25382, d198705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d25383 q = 0) : d198706 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d198706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25383, d198706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d25388 q = 0) : d198711 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25388, d198711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25388, d198711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d25389 q = 0) : d198712 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25389, d198712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25389, d198712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d25390 q = 0) : d198713 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25390, d198713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d25390, d198713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d25391 q = 0) : d198714 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25391, d198714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25391, d198714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18734 (p : Pattern) (selected : d25397 p = 0) : d198720 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25392 q = 0) : d198715 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25392, d198715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18732 q selected
    | true =>
      simp only [d25392, d198715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18733 q selected
  have h2 (q : Pattern) (selected : d25393 q = 0) : d198716 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25393, d198716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25393, d198716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d25394 q = 0) : d198717 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25394, d198717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25394, d198717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d25395 q = 0) : d198718 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25395, d198718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25395, d198718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d25396 q = 0) : d198719 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25396, d198719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25396, d198719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d25397 q = 0) : d198720 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25397, d198720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25397, d198720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18735 (p : Pattern) (selected : d25400 p = 0) : d198723 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25378 q = 0) : d198701 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d198701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18730 q selected
    | true =>
      simp only [d25378, d198701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d25379 q = 0) : d198702 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d198702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25379, d198702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d25382 q = 0) : d198705 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d198705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18731 q selected
    | true =>
      simp only [d25382, d198705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d25383 q = 0) : d198706 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d198706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25383, d198706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d25384 q = 0) : d198707 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25384, d198707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25384, d198707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d25385 q = 0) : d198708 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25385, d198708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d25385, d198708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d25386 q = 0) : d198709 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25386, d198709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d25386, d198709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d25400 q = 0) : d198723 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25400, d198723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d25400, d198723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro18736 (p : Pattern) (selected : d25401 p = 0) : d198724 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25382 q = 0) : d198705 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d198705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18731 q selected
    | true =>
      simp only [d25382, d198705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d25383 q = 0) : d198706 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d198706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25383, d198706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d25388 q = 0) : d198711 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25388, d198711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25388, d198711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d25389 q = 0) : d198712 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25389, d198712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25389, d198712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d25390 q = 0) : d198713 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25390, d198713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d25390, d198713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d25401 q = 0) : d198724 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25401, d198724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d25401, d198724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro18737 (p : Pattern) (selected : d25407 p = 0) : d198730 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25392 q = 0) : d198715 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25392, d198715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18732 q selected
    | true =>
      simp only [d25392, d198715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18733 q selected
  have h2 (q : Pattern) (selected : d25393 q = 0) : d198716 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25393, d198716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25393, d198716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d25394 q = 0) : d198717 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25394, d198717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25394, d198717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d25395 q = 0) : d198718 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25395, d198718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25395, d198718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d25396 q = 0) : d198719 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25396, d198719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25396, d198719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d25402 q = 0) : d198725 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25402, d198725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18735 q selected
    | true =>
      simp only [d25402, d198725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18736 q selected
  have h7 (q : Pattern) (selected : d25403 q = 0) : d198726 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25403, d198726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25403, d198726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d25404 q = 0) : d198727 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25404, d198727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d25404, d198727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d25405 q = 0) : d198728 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25405, d198728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25405, d198728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d25406 q = 0) : d198729 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25406, d198729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25406, d198729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d25407 q = 0) : d198730 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25407, d198730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d25407, d198730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro18738 (p : Pattern) (selected : d25412 p = 0) : d198735 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25378 q = 0) : d198701 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d198701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18730 q selected
    | true =>
      simp only [d25378, d198701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d25379 q = 0) : d198702 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d198702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25379, d198702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d25382 q = 0) : d198705 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d198705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18731 q selected
    | true =>
      simp only [d25382, d198705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d25383 q = 0) : d198706 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d198706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25383, d198706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d25384 q = 0) : d198707 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25384, d198707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25384, d198707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d25385 q = 0) : d198708 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25385, d198708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d25385, d198708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d25411 q = 0) : d198734 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25411, d198734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25411, d198734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d25412 q = 0) : d198735 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25412, d198735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25412, d198735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro18739 (p : Pattern) (selected : d25414 p = 0) : d198737 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25382 q = 0) : d198705 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d198705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18731 q selected
    | true =>
      simp only [d25382, d198705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d25383 q = 0) : d198706 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d198706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25383, d198706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d25388 q = 0) : d198711 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25388, d198711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25388, d198711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d25389 q = 0) : d198712 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25389, d198712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25389, d198712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d25413 q = 0) : d198736 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25413, d198736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25413, d198736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d25414 q = 0) : d198737 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25414, d198737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25414, d198737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18740 (p : Pattern) (selected : d25421 p = 0) : d198744 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25378 q = 0) : d198701 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d198701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18730 q selected
    | true =>
      simp only [d25378, d198701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d25379 q = 0) : d198702 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d198702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25379, d198702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d25382 q = 0) : d198705 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d198705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18731 q selected
    | true =>
      simp only [d25382, d198705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d25383 q = 0) : d198706 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d198706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25383, d198706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d25384 q = 0) : d198707 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25384, d198707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25384, d198707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d25419 q = 0) : d198742 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25419, d198742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25419, d198742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d25420 q = 0) : d198743 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25420, d198743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d25420, d198743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d25421 q = 0) : d198744 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25421, d198744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25421, d198744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro18741 (p : Pattern) (selected : d25424 p = 0) : d198747 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25382 q = 0) : d198705 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d198705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18731 q selected
    | true =>
      simp only [d25382, d198705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d25383 q = 0) : d198706 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d198706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25383, d198706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d25388 q = 0) : d198711 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25388, d198711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25388, d198711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d25422 q = 0) : d198745 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25422, d198745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25422, d198745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d25423 q = 0) : d198746 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25423, d198746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d25423, d198746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d25424 q = 0) : d198747 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25424, d198747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25424, d198747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro18742 (p : Pattern) (selected : d25432 p = 0) : d198755 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1 q = 0) : d0 q = 1 := by
    change (1 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d127 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d127, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d127, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13 q = 0) : d127 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d128 q = 0) : d51979 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d128, d51979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d128, d51979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14 q = 0) : d51866 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d129 q = 0) : d51980 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d129, d51980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d129, d51980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d15 q = 0) : d51867 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, d51867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15, d51867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d130 q = 0) : d51981 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d130, d51981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d130, d51981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d16 q = 0) : d51868 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d16, d51868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d16, d51868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d131 q = 0) : d51982 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d131, d51982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d131, d51982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d25432 q = 0) : d198755 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d25432, d198755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d25432, d198755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h11 p selected
theorem eqIntro18743 (p : Pattern) (selected : d25438 p = 0) : d198761 p = 1 := by
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
  have h3 (q : Pattern) (selected : d25428 q = 0) : d198751 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25428, d198751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25428, d198751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d537 q = 0) : d52284 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d537, d52284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro276 q selected
    | true =>
      simp only [d537, d52284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d538 q = 0) : d52285 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d538, d52285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d538, d52285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d25429 q = 0) : d198752 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25429, d198752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d25429, d198752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d25430 q = 0) : d198753 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25430, d198753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25430, d198753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d25431 q = 0) : d198754 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25431, d198754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d25431, d198754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d313 q = 0) : d52112 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d52112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro234 q selected
    | true =>
      simp only [d313, d52112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d314 q = 0) : d52113 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d52113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d314, d52113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d25210 q = 0) : d198576 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25210, d198576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d25210, d198576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d25433 q = 0) : d198756 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25433, d198756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18742 q selected
    | true =>
      simp only [d25433, d198756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d25434 q = 0) : d198757 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25434, d198757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d25434, d198757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d25435 q = 0) : d198758 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25435, d198758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d25435, d198758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d25436 q = 0) : d198759 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25436, d198759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d25436, d198759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d25437 q = 0) : d198760 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25437, d198760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d25437, d198760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d25438 q = 0) : d198761 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25438, d198761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d25438, d198761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro18744 (p : Pattern) (selected : d25443 p = 0) : d198766 p = 1 := by
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
  have h3 (q : Pattern) (selected : d25210 q = 0) : d198576 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25210, d198576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25210, d198576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h6 (q : Pattern) (selected : d9796 q = 0) : d101317 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9796, d101317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d9796, d101317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d25211 q = 0) : d198577 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25211, d198577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25211, d198577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d25212 q = 0) : d198578 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25212, d198578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d25212, d198578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d25219 q = 0) : d198585 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25219, d198585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d25219, d198585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d25220 q = 0) : d198586 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25220, d198586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d25220, d198586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d25443 q = 0) : d198766 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25443, d198766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d25443, d198766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro18745 (p : Pattern) (selected : d25451 p = 0) : d198774 p = 1 := by
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
  have h3 (q : Pattern) (selected : d25210 q = 0) : d198576 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25210, d198576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25210, d198576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d25449 q = 0) : d198772 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25449, d198772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25449, d198772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d25450 q = 0) : d198773 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25450, d198773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d25450, d198773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133 q = 0) : d51984 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro204 q selected
    | true =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d134 q = 0) : d51985 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9796 q = 0) : d101317 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9796, d101317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d9796, d101317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d25219 q = 0) : d198585 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25219, d198585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d25219, d198585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d25220 q = 0) : d198586 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25220, d198586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d25220, d198586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d25451 q = 0) : d198774 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25451, d198774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d25451, d198774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro18746 (p : Pattern) (selected : d25457 p = 0) : d198780 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25439 q = 0) : d198762 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25439, d198762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18743 q selected
    | true =>
      simp only [d25439, d198762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d25440 q = 0) : d198763 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25440, d198763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d25440, d198763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d25441 q = 0) : d198764 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25441, d198764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25441, d198764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d25442 q = 0) : d198765 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25442, d198765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25442, d198765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d25444 q = 0) : d198767 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25444, d198767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18744 q selected
    | true =>
      simp only [d25444, d198767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d25445 q = 0) : d198768 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25445, d198768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d25445, d198768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d25446 q = 0) : d198769 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25446, d198769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25446, d198769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d25447 q = 0) : d198770 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25447, d198770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d25447, d198770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d25448 q = 0) : d198771 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25448, d198771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d25448, d198771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d25452 q = 0) : d198775 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25452, d198775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18745 q selected
    | true =>
      simp only [d25452, d198775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d25453 q = 0) : d198776 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25453, d198776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d25453, d198776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d25454 q = 0) : d198777 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25454, d198777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25454, d198777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d25455 q = 0) : d198778 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25455, d198778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d25455, d198778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d25222 q = 0) : d198588 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25222, d198588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18702 q selected
    | true =>
      simp only [d25222, d198588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d25223 q = 0) : d198589 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25223, d198589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d25223, d198589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d25224 q = 0) : d198590 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25224, d198590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25224, d198590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d25225 q = 0) : d198591 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25225, d198591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d25225, d198591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d25456 q = 0) : d198779 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25456, d198779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d25456, d198779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d25457 q = 0) : d198780 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25457, d198780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d25457, d198780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro18747 (p : Pattern) (selected : d25461 p = 0) : d198784 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25222 q = 0) : d198588 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25222, d198588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18702 q selected
    | true =>
      simp only [d25222, d198588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d25223 q = 0) : d198589 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25223, d198589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d25223, d198589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d25224 q = 0) : d198590 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25224, d198590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25224, d198590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d25225 q = 0) : d198591 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25225, d198591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25225, d198591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d25 q = 0) : d51877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d26 q = 0) : d51878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d27 q = 0) : d51879 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d28 q = 0) : d51880 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d25226 q = 0) : d198592 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25226, d198592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d25226, d198592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d29 q = 0) : d51881 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, d51881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d29, d51881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d25461 q = 0) : d198784 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25461, d198784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d25461, d198784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro18748 (p : Pattern) (selected : d25467 p = 0) : d198790 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25458 q = 0) : d198781 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25458, d198781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18746 q selected
    | true =>
      simp only [d25458, d198781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18703 q selected
  have h2 (q : Pattern) (selected : d25459 q = 0) : d198782 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25459, d198782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25459, d198782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d25460 q = 0) : d198783 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25460, d198783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25460, d198783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d25462 q = 0) : d198785 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25462, d198785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18703 q selected
    | true =>
      simp only [d25462, d198785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18747 q selected
  have h5 (q : Pattern) (selected : d25463 q = 0) : d198786 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25463, d198786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25463, d198786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d25464 q = 0) : d198787 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25464, d198787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25464, d198787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d25465 q = 0) : d198788 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25465, d198788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d25465, d198788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d25228 q = 0) : d198594 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25228, d198594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18703 q selected
    | true =>
      simp only [d25228, d198594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18685 q selected
  have h9 (q : Pattern) (selected : d25229 q = 0) : d198595 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25229, d198595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25229, d198595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d25230 q = 0) : d198596 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25230, d198596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25230, d198596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d25111 q = 0) : d198477 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25111, d198477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18685 q selected
    | true =>
      simp only [d25111, d198477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro188 q selected
  have h12 (q : Pattern) (selected : d25112 q = 0) : d198478 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25112, d198478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25112, d198478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d25113 q = 0) : d198479 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25113, d198479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25113, d198479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d25231 q = 0) : d198597 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25231, d198597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d25231, d198597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d25466 q = 0) : d198789 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25466, d198789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d25466, d198789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d25467 q = 0) : d198790 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25467, d198790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d25467, d198790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro18749 (p : Pattern) (selected : d25473 p = 0) : d198796 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d25468 q = 0) : d198791 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25468, d198791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18748 q selected
    | true =>
      simp only [d25468, d198791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d25469 q = 0) : d198792 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25469, d198792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25469, d198792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d25378 q = 0) : d198701 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d198701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18730 q selected
    | true =>
      simp only [d25378, d198701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d25379 q = 0) : d198702 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d198702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25379, d198702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d25470 q = 0) : d198793 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25470, d198793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d25470, d198793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d25471 q = 0) : d198794 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25471, d198794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d25471, d198794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d25472 q = 0) : d198795 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25472, d198795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d25472, d198795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d25473 q = 0) : d198796 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25473, d198796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d25473, d198796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
end NetHack.Soko22Hazard87
